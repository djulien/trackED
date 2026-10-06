"""
audio_analysis.py -- heavier, optional audio analysis for waveform_tab.py:

  - demucs 2-stem separation (vocals / instrumental), cached as WAVs next to
    the audio file using the old audio_tab.py naming:
        <stem>-vocals.wav, <stem>-non_vocals.wav
  - partitioning the timeline into vocal-only / instrumental-only / mixed /
    silent regions from the stems' energy
  - Whisper transcription of the vocal parts of a time range (for a range
    mark's label), with the model picked from available RAM unless the
    user overrides it

Like timing_helpers.py, nothing here touches Tk, so it can run in worker
threads and be tested on its own. All heavy imports (torch, demucs,
faster_whisper, ...) happen lazily inside functions so importing this
module is cheap and never blocks the UI.

Third-party packages used (all optional, all permissive licenses):
  demucs          MIT          stem separation (pulls in torch, BSD-3)
  faster-whisper  MIT          preferred transcription backend
  whisperx        BSD-2-Clause optional fallback backend (built on faster-whisper)
  openai-whisper  MIT          optional fallback backend
  psutil          BSD-3        optional, for the free-RAM check
  librosa         ISC          optional, for the genre / mood estimate
The separation logic follows the old audio_tab.py (this project's own
code); the RAM-based model choice follows auto-timing.py (also ours).
"""

from __future__ import annotations

import gc
import os
import shutil
import subprocess
import threading
import time
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

try:
    import numpy as np
except ImportError:
    np = None  # type: ignore

try:
    import soundfile as sf
except ImportError:
    sf = None  # type: ignore

ProgressCb = Optional[Callable[[str], None]]

# Region kinds (names kept from audio_tab.py; "silent" is new -- the old
# tab lumped silence into "mixed", which inflated the mixed count).
KINDS = ("vocal", "novocal", "mixed", "silent")
VOCAL_KINDS = ("vocal", "mixed")  # regions that contain singing/speech

# ---------------------------------------------------------------------------
# Availability probes (lazy -- torch is slow to import)
# ---------------------------------------------------------------------------
_probe_cache: Dict[str, bool] = {}


def _importable(name: str) -> bool:
    if name not in _probe_cache:
        import importlib.util
        try:
            _probe_cache[name] = importlib.util.find_spec(name) is not None
        except Exception:
            _probe_cache[name] = False
    return _probe_cache[name]


def clear_probe_cache() -> None:
    """Forget the import checks (after the Install button added packages)."""
    import importlib
    _probe_cache.clear()
    importlib.invalidate_caches()


def demucs_available() -> bool:
    """Cheap check (doesn't import torch): are demucs and torch installed?"""
    return _importable("demucs") and _importable("torch")


def whisper_backends() -> List[str]:
    """Installed transcription backends, in the order they'll be tried."""
    out = []
    if _importable("faster_whisper"):
        out.append("faster-whisper")
    if _importable("whisperx"):
        out.append("whisperx")
    if _importable("whisper"):
        out.append("openai-whisper")
    return out


# ---------------------------------------------------------------------------
# Stem files (same names/location as the old audio_tab.py)
# ---------------------------------------------------------------------------

def stem_paths(filepath: str) -> Tuple[Path, Path]:
    p = Path(filepath)
    return p.with_name(p.stem + "-vocals.wav"), p.with_name(p.stem + "-non_vocals.wav")


def stems_are_fresh(filepath: str) -> bool:
    """True if both stem WAVs exist and are newer than the audio file."""
    try:
        audio_mtime = Path(filepath).stat().st_mtime
    except OSError:
        return False
    for sp in stem_paths(filepath):
        try:
            if not sp.is_file() or sp.stat().st_mtime < audio_mtime:
                return False
        except OSError:
            return False
    return True


def decode_for_demucs(path: str, sr: int, channels: int):
    """The whole file as float32 [channels, samples] at sr. demucs' own
    reader (demucs.audio.AudioFile) runs ffprobe, which is often missing on
    Windows ("[WinError 2] The system cannot find the file specified"), so
    decode here instead: ffmpeg if it's on PATH, else soundfile, else
    miniaudio. Raises RuntimeError naming what's needed."""
    if np is None:
        raise RuntimeError("numpy not installed")
    ffmpeg = shutil.which("ffmpeg")
    if ffmpeg:
        proc = subprocess.run([ffmpeg, "-v", "error", "-i", path, "-vn", "-ac", str(channels), "-ar", str(sr),
                               "-f", "f32le", "-"], capture_output=True, timeout=1800)
        if proc.returncode == 0 and proc.stdout:
            return np.frombuffer(proc.stdout, dtype=np.float32).reshape(-1, channels).T.copy()
    data = None
    if sf is not None:
        try:
            data, file_sr = sf.read(path, dtype="float32", always_2d=True)
            data = data.T
        except Exception:
            data = None
    if data is None:
        try:
            import miniaudio
            dec = miniaudio.decode_file(path, output_format=miniaudio.SampleFormat.FLOAT32,
                                        nchannels=channels, sample_rate=sr)
            return np.asarray(dec.samples, dtype=np.float32).reshape(-1, channels).T.copy()
        except ImportError:
            pass
        except Exception as exc:
            raise RuntimeError(f"couldn't decode {Path(path).name}: {exc}")
        raise RuntimeError(f"can't decode {Path(path).name} without ffmpeg (or soundfile/miniaudio)")
    if data.shape[0] != channels:
        data = np.repeat(data.mean(axis=0, keepdims=True), channels, axis=0)
    if file_sr != sr and data.shape[1]:
        n_out = int(round(data.shape[1] * sr / file_sr))
        x_old = np.arange(data.shape[1], dtype=np.float64)
        x_new = np.linspace(0, data.shape[1] - 1, n_out)
        data = np.stack([np.interp(x_new, x_old, ch) for ch in data]).astype(np.float32)
    return np.ascontiguousarray(data, dtype=np.float32)


def explain_error(error: BaseException, what: str = "this") -> str:
    """One readable line plus what to do about it, for errors from stem
    separation / transcription / mood (shown in the text panel)."""
    msg = str(error) or error.__class__.__name__
    if isinstance(error, FileNotFoundError):
        name = getattr(error, "filename", None)
        if name and Path(str(name)).suffix.lower() in (".mp3", ".wav", ".flac", ".m4a", ".mp4", ".ogg"):
            return f"{msg}\n  The audio file {name} can't be found (moved or renamed?)."
        prog = Path(str(name)).name if name else "a helper program (most likely ffmpeg or ffprobe)"
        return (f"{msg}\n  {what} needed {prog}, which isn't on this computer's PATH. "
                "Install ffmpeg with the \u26a0 Install button (or from ffmpeg.org) and restart trackED.")
    low = msg.lower()
    if isinstance(error, MemoryError) or "out of memory" in low or "cuda out of memory" in low:
        return f"{msg}\n  Not enough memory. Close other programs, or pick a smaller Whisper model."
    if isinstance(error, PermissionError):
        return f"{msg}\n  trackED couldn't write next to the audio file; check that folder's permissions."
    if "no module named" in low:
        return f"{msg}\n  A package is missing: use the \u26a0 Install button in the upper right corner."
    if "urlopen" in low or "connection" in low or "download" in low:
        return (f"{msg}\n  The first run downloads a model from the internet; "
                "check the network connection and try again.")
    return msg


def separate_stems(filepath: str, progress_cb: ProgressCb = None) -> Tuple[Any, Any, int]:
    """Run demucs htdemucs and save <stem>-vocals.wav / <stem>-non_vocals.wav.
    Returns (vocals_mono, non_vocals_mono, sample_rate) as numpy arrays
    (so the caller can partition without re-reading the files).
    Raises on failure. Ported from audio_tab.py's _run_demucs_and_partition."""
    if np is None:
        raise RuntimeError("numpy not installed")
    if not demucs_available():
        raise RuntimeError("demucs/torch not installed (pip install demucs)")

    def report(msg):
        if progress_cb:
            progress_cb(msg)

    import torch
    from demucs.pretrained import get_model
    from demucs.apply import apply_model

    report("Loading demucs model... (5%)")
    model = get_model("htdemucs")
    model.eval()
    device = "cuda" if torch.cuda.is_available() else "cpu"
    if device == "cuda":
        model.cuda()

    report("Decoding audio for demucs... (15%)")
    wav = torch.from_numpy(decode_for_demucs(filepath, int(model.samplerate), int(model.audio_channels)))
    ref = wav.mean(0)
    wav = (wav - ref.mean()) / (ref.std() + 1e-8)
    audio_len = int(wav.shape[-1])

    def demucs_callback(info: dict):
        try:
            offset = float(info.get("segment_offset", 0) or 0)
            total = float(info.get("audio_length", audio_len) or audio_len)
            if total > 0 and info.get("state", "") == "end":
                report(f"Separating stems... ({20 + int(min(1.0, offset / total) * 65)}%)")
        except Exception:
            pass

    report("Running demucs separation... (20%)")
    kwargs = dict(device=device, shifts=1, split=True, overlap=0.25, progress=False)
    with torch.no_grad():
        try:
            sources = apply_model(model, wav[None], callback=demucs_callback, **kwargs)[0]
        except TypeError:
            # demucs 4.0.1 (the PyPI release) has no callback= parameter
            sources = apply_model(model, wav[None], **kwargs)[0]
    sources = sources * (ref.std() + 1e-8) + ref.mean()

    names = list(model.sources)
    vocals = sources[names.index("vocals")]
    novoc = sources.sum(0) - vocals

    voc_path, nov_path = stem_paths(filepath)
    if sf is not None:
        report("Saving stem files... (90%)")
        sf.write(str(voc_path), vocals.cpu().numpy().T, model.samplerate)
        sf.write(str(nov_path), novoc.cpu().numpy().T, model.samplerate)
    else:
        report("soundfile not installed -- stems not saved (will re-run next time)")

    voc_mono = vocals.mean(0).cpu().numpy()
    nov_mono = novoc.mean(0).cpu().numpy()
    sr = int(model.samplerate)
    del model, sources, wav
    gc.collect()
    return voc_mono, nov_mono, sr


def load_stems_mono(filepath: str) -> Tuple[Any, Any, int]:
    """Read the cached stem WAVs as mono float32 arrays."""
    if sf is None or np is None:
        raise RuntimeError("numpy + soundfile are needed to read cached stems")
    voc_path, nov_path = stem_paths(filepath)
    voc, sr_v = sf.read(str(voc_path), dtype="float32", always_2d=True)
    nov, _sr_n = sf.read(str(nov_path), dtype="float32", always_2d=True)
    return voc.mean(axis=1), nov.mean(axis=1), int(sr_v)


def _bin_rms(x, n_bins: int):
    """RMS energy of x in n_bins equal bins (vectorized)."""
    n = len(x)
    edges = (np.arange(n_bins + 1, dtype=np.float64) * n / n_bins).astype(np.int64)
    sq = np.asarray(x, dtype=np.float64) ** 2
    csum = np.concatenate(([0.0], np.cumsum(sq)))
    counts = np.diff(edges)
    sums = csum[edges[1:]] - csum[edges[:-1]]
    with np.errstate(invalid="ignore", divide="ignore"):
        rms = np.sqrt(np.where(counts > 0, sums / np.maximum(counts, 1), 0.0))
    return rms.astype(np.float32)


def partition_regions(voc_mono, nov_mono, duration: float, n_bins: int = 2000) -> List[Dict[str, Any]]:
    """Classify each of n_bins time slices as vocal / novocal / mixed /
    silent and collapse runs into regions [{"start","end","kind"}] in
    seconds. Thresholds as in audio_tab.py (adaptive: 40% of each stem's
    60th-percentile energy)."""
    if np is None or len(voc_mono) == 0 or n_bins < 2 or not duration:
        return []
    voc_e = _bin_rms(voc_mono, n_bins)
    nov_e = _bin_rms(nov_mono, n_bins)
    v_th = max(float(np.percentile(voc_e, 60)) * 0.4, 1e-5)
    n_th = max(float(np.percentile(nov_e, 60)) * 0.4, 1e-5)
    v, nv = voc_e > v_th, nov_e > n_th
    kinds = np.where(v & nv, 2, np.where(v, 0, np.where(nv, 1, 3)))  # index into KINDS

    regions: List[Dict[str, Any]] = []
    change = np.flatnonzero(np.diff(kinds)) + 1
    starts = np.concatenate(([0], change))
    ends = np.concatenate((change, [n_bins]))
    for a, b in zip(starts.tolist(), ends.tolist()):
        regions.append({
            "start": a / n_bins * duration,
            "end": duration if b >= n_bins else b / n_bins * duration,
            "kind": KINDS[int(kinds[a])],
        })
    return regions


def analyze_stems(filepath: str, duration: float, n_bins: int = 2000,
                  progress_cb: ProgressCb = None, force: bool = False) -> Tuple[List[Dict[str, Any]], bool]:
    """Separate (or reuse cached stems) and partition.
    Returns (regions, reused_cached_stems). Raises on failure."""
    reused = False
    voc = nov = None
    if not force and stems_are_fresh(filepath) and sf is not None:
        if progress_cb:
            progress_cb("Loading cached stem files... (0%)")
        try:
            voc, nov, _sr = load_stems_mono(filepath)
            reused = True
        except Exception:
            voc = nov = None
    if voc is None:
        voc, nov, _sr = separate_stems(filepath, progress_cb)
    if progress_cb:
        progress_cb("Partitioning regions... (95%)")
    return partition_regions(voc, nov, duration, n_bins), reused


def smooth_regions(regions: List[Dict[str, Any]], min_seconds: float) -> List[Dict[str, Any]]:
    """Absorb regions shorter than min_seconds into their neighbors, so a
    brief gap or blip doesn't split a stem into many alternating pieces.
    The shortest short region goes first: if both neighbors are the same
    kind, the three become one; otherwise it joins the longer neighbor.
    Adjacent regions of the same kind are always merged."""
    rs = [dict(r) for r in regions]

    def coalesce(items):
        out = []
        for r in items:
            if out and out[-1]["kind"] == r["kind"]:
                out[-1]["end"] = r["end"]
            else:
                out.append(r)
        return out

    rs = coalesce(rs)
    if min_seconds <= 0:
        return rs
    while len(rs) > 1:
        i = min(range(len(rs)), key=lambda k: rs[k]["end"] - rs[k]["start"])
        if rs[i]["end"] - rs[i]["start"] >= min_seconds:
            break
        prev_r = rs[i - 1] if i > 0 else None
        next_r = rs[i + 1] if i + 1 < len(rs) else None
        if prev_r and next_r and prev_r["kind"] == next_r["kind"]:
            prev_r["end"] = next_r["end"]
            del rs[i:i + 2]
        elif prev_r and (not next_r or (prev_r["end"] - prev_r["start"]) >= (next_r["end"] - next_r["start"])):
            prev_r["end"] = rs[i]["end"]
            del rs[i]
        else:
            next_r["start"] = rs[i]["start"]
            del rs[i]
        rs = coalesce(rs)
    return rs


def regions_for_kinds(regions: List[Dict[str, Any]], kinds, merge_adjacent: bool = True) -> List[Tuple[float, float]]:
    """(start, end) spans of the regions whose kind is in `kinds`. With
    merge_adjacent, touching regions (e.g. vocal then mixed) become one
    span; otherwise each region stays its own span."""
    spans: List[Tuple[float, float]] = []
    for r in regions:
        if r.get("kind") not in kinds:
            continue
        if merge_adjacent and spans and abs(spans[-1][1] - r["start"]) < 1e-6:
            spans[-1] = (spans[-1][0], r["end"])
        else:
            spans.append((r["start"], r["end"]))
    return spans


def region_counts(regions: List[Dict[str, Any]]) -> Dict[str, int]:
    counts = {k: 0 for k in KINDS}
    for r in regions:
        counts[r.get("kind", "mixed")] = counts.get(r.get("kind", "mixed"), 0) + 1
    return counts


def region_seconds(regions: List[Dict[str, Any]]) -> Dict[str, float]:
    secs = {k: 0.0 for k in KINDS}
    for r in regions:
        secs[r.get("kind", "mixed")] = secs.get(r.get("kind", "mixed"), 0.0) + (r["end"] - r["start"])
    return secs


# ---------------------------------------------------------------------------
# Whisper transcription
# ---------------------------------------------------------------------------

WHISPER_MODELS = ["tiny", "base", "small", "medium", "large-v3"]
WHISPER_SR = 16000


def available_ram_gb() -> float:
    """Best-effort available RAM in GB (psutil, else /proc/meminfo, else 4)."""
    try:
        import psutil
        return psutil.virtual_memory().available / (1024 ** 3)
    except Exception:
        pass
    try:
        with open("/proc/meminfo", "r", encoding="utf-8") as f:
            for line in f:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) / (1024 ** 2)
    except Exception:
        pass
    return 4.0


def default_whisper_model(free_gb: Optional[float] = None) -> str:
    """Largest model that comfortably fits in free RAM on CPU (int8).
    Rough peak use: tiny ~1 GB, base ~1.5, small ~2.5, medium ~5,
    large-v3 ~8 (with headroom for the rest of the app and the decode)."""
    free = available_ram_gb() if free_gb is None else free_gb
    if free < 2.5:
        return "tiny"
    if free < 4.0:
        return "base"
    if free < 6.5:
        return "small"
    if free < 10.0:
        return "medium"
    return "large-v3"


_model_lock = threading.Lock()
_loaded: Dict[str, Any] = {"key": None, "model": None}


def _get_model(backend: str, size: str):
    """Load (or reuse) one model; only one is kept in memory at a time."""
    key = (backend, size)
    with _model_lock:
        if _loaded["key"] == key:
            return _loaded["model"]
        _loaded["model"] = None
        _loaded["key"] = None
        gc.collect()
        if backend == "faster-whisper":
            from faster_whisper import WhisperModel
            model = WhisperModel(size, device="cpu", compute_type="int8")
        elif backend == "whisperx":
            os.environ.setdefault("CUDA_VISIBLE_DEVICES", "")
            import whisperx
            model = whisperx.load_model(size, device="cpu", compute_type="int8")
        else:
            import whisper
            model = whisper.load_model(size, device="cpu")
        _loaded["model"], _loaded["key"] = model, key
        return model


def unload_model() -> None:
    with _model_lock:
        _loaded["model"] = None
        _loaded["key"] = None
    gc.collect()


def _decode_16k_mono(path: str, start: float, end: float, sr: int = WHISPER_SR):
    """float32 mono samples at `sr` (16 kHz by default) for [start, end) of path."""
    WHISPER_SR_ = sr
    ffmpeg = shutil.which("ffmpeg")
    dur = max(0.0, end - start)
    if ffmpeg:
        proc = subprocess.run(
            [ffmpeg, "-v", "error", "-ss", f"{start:.3f}", "-t", f"{dur:.3f}", "-i", path,
             "-ac", "1", "-ar", str(WHISPER_SR_), "-f", "f32le", "-"],
            capture_output=True, timeout=300,
        )
        if proc.returncode == 0 and proc.stdout:
            return np.frombuffer(proc.stdout, dtype=np.float32).copy()
    if sf is None:
        raise RuntimeError("need ffmpeg or soundfile to read audio for transcription")
    with sf.SoundFile(path) as f:
        sr = f.samplerate
        f.seek(int(start * sr))
        data = f.read(int(dur * sr), dtype="float32", always_2d=True).mean(axis=1)
    if sr == WHISPER_SR_ or len(data) == 0:
        return data.astype(np.float32)
    n_out = int(len(data) * WHISPER_SR_ / sr)
    return np.interp(np.linspace(0, len(data) - 1, n_out), np.arange(len(data)), data).astype(np.float32)


def vocal_spans(regions: List[Dict[str, Any]], start: float, end: float) -> List[Tuple[float, float]]:
    """Parts of [start, end) that fall in vocal-containing regions."""
    spans = []
    for r in regions:
        if r.get("kind") not in VOCAL_KINDS:
            continue
        a, b = max(start, r["start"]), min(end, r["end"])
        if b > a:
            if spans and a - spans[-1][1] < 1e-6:
                spans[-1] = (spans[-1][0], b)
            else:
                spans.append((a, b))
    return spans


def transcribe_range(filepath: str, start: float, end: float, model_size: Optional[str] = None,
                     regions: Optional[List[Dict[str, Any]]] = None, language: Optional[str] = None,
                     progress_cb: ProgressCb = None) -> Dict[str, Any]:
    """Transcribe the vocal portions of [start, end).

    Uses the cached vocal stem when available (falls back to the original
    mix), and when stem regions are known, silences everything outside
    vocal/mixed regions first so Whisper doesn't try to "hear" words in
    instrumental parts. Returns {"text", "model", "backend", "source",
    "seconds_voiced", "elapsed"}. Raises if no backend is installed."""
    if np is None:
        raise RuntimeError("numpy not installed")
    backends = whisper_backends()
    if not backends:
        raise RuntimeError("no Whisper backend installed (pip install faster-whisper)")
    t0 = time.time()
    size = model_size or default_whisper_model()

    def report(msg):
        if progress_cb:
            progress_cb(msg)

    voc_path, _ = stem_paths(filepath)
    source = "vocal stem" if stems_are_fresh(filepath) else "original mix"
    audio_path = str(voc_path) if source == "vocal stem" else filepath

    report(f"Reading {source}...")
    audio = _decode_16k_mono(audio_path, start, end)
    voiced = end - start
    if regions:
        spans = vocal_spans(regions, start, end)
        mask = np.zeros(len(audio), dtype=bool)
        for a, b in spans:
            mask[int((a - start) * WHISPER_SR):int((b - start) * WHISPER_SR)] = True
        audio = np.where(mask, audio, 0.0).astype(np.float32)
        voiced = sum(b - a for a, b in spans)
        if voiced <= 0.05:
            return {"text": "", "model": size, "backend": None, "source": source,
                    "seconds_voiced": 0.0, "elapsed": time.time() - t0}

    last_error = None
    for backend in backends:
        try:
            report(f"Loading {backend} '{size}' model...")
            model = _get_model(backend, size)
            report(f"Transcribing {voiced:.1f}s of vocals ({backend} {size})...")
            if backend == "faster-whisper":
                segs, _info = model.transcribe(audio, language=language, vad_filter=True,
                                               beam_size=5, condition_on_previous_text=False)
                raw = [(seg.start, seg.end, seg.text) for seg in segs]
            else:
                if backend == "whisperx":
                    result = model.transcribe(audio, batch_size=1, language=language)
                else:
                    result = model.transcribe(audio, language=language, fp16=False,
                                              condition_on_previous_text=False)
                raw = [(sg.get("start", 0.0), sg.get("end", 0.0), sg.get("text", ""))
                       for sg in result.get("segments", [])]
            # Whisper's phrase timings, moved from the slice to the file's timeline.
            segments = [(start + float(a), start + float(b), " ".join(str(t).split()))
                        for a, b, t in raw if str(t).strip()]
            text = " ".join(t for _a, _b, t in segments)
            return {"text": text, "segments": segments, "model": size, "backend": backend, "source": source,
                    "seconds_voiced": voiced, "elapsed": time.time() - t0}
        except Exception as exc:
            last_error = exc
            unload_model()
            continue
    raise RuntimeError(f"transcription failed: {last_error}")


# ---------------------------------------------------------------------------
# Genre / mood estimate (heuristic)
# ---------------------------------------------------------------------------
# Rule-based, ported from this project's auto-timing.py
# (estimate_genre_and_emotion): a handful of averaged spectral features plus
# tempo, scored against simple rules. It's a rough guess, not a classifier.

GENRE_SR = 22050

MOOD_PALETTES = {
    "joyful / energetic": [("#FF6B6B", "Coral Red"), ("#FFE66D", "Sunny Yellow"), ("#4ECDC4", "Aqua"), ("#1A1A2E", "Deep Navy")],
    "warm / content": [("#FF9F43", "Warm Amber"), ("#FEC84B", "Golden"), ("#E17055", "Soft Terracotta"), ("#2D3436", "Charcoal")],
    "tense / aggressive": [("#E74C3C", "Blood Red"), ("#2C3E50", "Dark Slate"), ("#F39C12", "Warning Orange"), ("#8E44AD", "Deep Purple")],
    "melancholic / reflective": [("#5B6EE1", "Midnight Blue"), ("#A29BFE", "Soft Lavender"), ("#636E72", "Cool Grey"), ("#2D3436", "Almost Black")],
    "intense / driving": [("#9B59B6", "Electric Purple"), ("#E74C3C", "Hot Red"), ("#1ABC9C", "Teal Pulse"), ("#2C3E50", "Night")],
    "neutral / balanced": [("#00B894", "Fresh Teal"), ("#FDCB6E", "Soft Gold"), ("#6C5CE7", "Muted Violet"), ("#2D3436", "Charcoal")],
}

_LYRIC_KEYWORDS = {
    "hip-hop / rap": ["rap", "beat", "flow", "mic", "rhyme", "hood", "street"],
    "rock": ["guitar", "rock", "scream", "fire", "night", "road"],
    "pop": ["love", "baby", "heart", "dance", "tonight", "feel"],
    "electronic / dance": ["bass", "drop", "synth", "club", "rave", "pulse"],
    "metal": ["scream", "dark", "blood", "fire", "death", "shadow"],
    "r&b / soul": ["love", "baby", "soul", "night", "feel", "touch"],
    "country / folk": ["road", "truck", "beer", "home", "heart", "whiskey"],
    "jazz": ["blue", "night", "soul", "swing", "moon"],
}


def genre_mood_available() -> bool:
    return _importable("librosa") and np is not None


def score_genre_mood(features: Dict[str, float], lyrics: str = "") -> Dict[str, Any]:
    """The rules themselves (pure: features in, estimate out).
    features: tempo, mean_rms, mean_cent, mean_bw, mean_contrast,
    mean_zcr, percussiveness."""
    tempo = features["tempo"]
    mean_rms, mean_cent = features["mean_rms"], features["mean_cent"]
    mean_bw, mean_contrast = features["mean_bw"], features["mean_contrast"]
    mean_zcr, perc = features["mean_zcr"], features["percussiveness"]

    def clip(v, lo, hi):
        return max(lo, min(hi, v))

    valence = clip(0.5 + 0.3 * (mean_cent / 4000 - 0.5) + 0.2 * (mean_contrast / 30 - 0.5), 0.0, 1.0)
    arousal = clip(0.4 * (tempo / 140) + 0.4 * (mean_rms * 10) + 0.2 * (perc / 5), 0.0, 1.0)

    scores = {g: 0.0 for g in ("electronic / dance", "pop", "rock", "hip-hop / rap", "r&b / soul", "metal",
                               "indie / alternative", "ambient / chill", "jazz", "classical / orchestral",
                               "country / folk")}
    if 120 <= tempo <= 140 and mean_rms > 0.08 and perc > 3:
        scores["electronic / dance"] += 2.5; scores["pop"] += 1.5
    if 90 <= tempo <= 110 and mean_cent < 2500:
        scores["hip-hop / rap"] += 2.0; scores["r&b / soul"] += 1.0
    if 110 <= tempo <= 140 and mean_contrast > 20 and mean_bw > 2000:
        scores["rock"] += 2.0; scores["indie / alternative"] += 1.0
    if tempo > 140 and mean_cent > 3000 and mean_zcr > 0.1:
        scores["metal"] += 2.5; scores["rock"] += 1.0
    if tempo < 90 and mean_rms < 0.06 and mean_cent < 2000:
        scores["ambient / chill"] += 2.5; scores["jazz"] += 1.0
    if 70 <= tempo <= 100 and mean_contrast < 18:
        scores["r&b / soul"] += 1.8; scores["pop"] += 1.0
    if mean_cent > 2800 and valence > 0.6 and 100 <= tempo <= 130:
        scores["pop"] += 2.0
    if mean_bw < 1800 and mean_zcr < 0.05 and tempo < 100:
        scores["classical / orchestral"] += 1.5; scores["jazz"] += 1.0
    text = (lyrics or "").lower()
    if "guitar" in text or (mean_contrast > 22 and 100 < tempo < 140):
        scores["country / folk"] += 1.2; scores["rock"] += 0.8
    for genre, words in _LYRIC_KEYWORDS.items():   # lyrics (e.g. from Transcribe) nudge the score
        hits = sum(1 for w in words if w in text)
        if hits:
            scores[genre] += hits * 0.8

    ranked = sorted(scores.items(), key=lambda kv: kv[1], reverse=True)
    best, best_score = ranked[0]
    total = sum(v for _, v in ranked) + 1e-6
    conf = clip((best_score / total) * 1.5, 0.15, 0.95)
    alternatives = []
    if conf < 0.55:
        for g, sc in ranked[1:4]:
            alt = clip((sc / total) * 1.5, 0.05, 0.95)
            if alt >= conf * 0.65:
                alternatives.append((g, round(alt, 2)))
    if best_score <= 0:
        best, conf = "unclear", 0.15

    if valence > 0.65 and arousal > 0.6:
        mood = "joyful / energetic"
    elif valence > 0.6 and arousal < 0.45:
        mood = "warm / content"
    elif valence < 0.4 and arousal > 0.55:
        mood = "tense / aggressive"
    elif valence < 0.4 and arousal < 0.4:
        mood = "melancholic / reflective"
    elif arousal > 0.7:
        mood = "intense / driving"
    else:
        mood = "neutral / balanced"
    return {"genre": best, "confidence": round(conf, 2), "alternatives": alternatives, "mood": mood,
            "energy": round(arousal, 2), "valence": round(valence, 2), "tempo": round(tempo, 1),
            "palette": MOOD_PALETTES[mood]}


def beats_available() -> bool:
    """Bars/Beats detection uses librosa too."""
    return genre_mood_available()


def detect_beats(filepath: str, progress_cb: ProgressCb = None) -> Dict[str, Any]:
    """Beat times for the whole file (librosa's beat tracker), with the
    onset strength and the bass energy at each beat (used to guess which
    beat starts a bar: timing_helpers.downbeat_phase).
    Returns {"tempo", "beats", "strength", "bass"}. Slow-ish: run it in a
    worker thread. Raises if librosa isn't installed."""
    if not beats_available():
        raise RuntimeError("librosa not installed")
    import librosa

    def report(msg):
        if progress_cb:
            progress_cb(msg)
    report("Decoding audio... (10%)")
    duration = None
    try:
        duration = librosa.get_duration(path=filepath)
    except Exception:
        pass
    y = _decode_16k_mono(filepath, 0.0, duration or 36000.0, sr=GENRE_SR)
    if len(y) == 0:
        raise RuntimeError("no audio decoded")
    sr, hop = GENRE_SR, 512
    report("Finding beats... (40%)")
    onset_env = librosa.onset.onset_strength(y=y, sr=sr, hop_length=hop)
    tempo, frames = librosa.beat.beat_track(onset_envelope=onset_env, sr=sr, hop_length=hop, units="frames")
    frames = np.asarray(frames, dtype=int)
    report("Measuring bass at each beat... (75%)")
    spec = np.abs(librosa.stft(y, hop_length=hop))
    freqs = librosa.fft_frequencies(sr=sr)
    low = spec[freqs < 150.0].sum(axis=0)
    frames = frames[frames < len(onset_env)]
    times = librosa.frames_to_time(frames, sr=sr, hop_length=hop)
    return {"tempo": float(np.atleast_1d(tempo)[0]), "beats": [float(t) for t in times],
            "strength": [float(onset_env[f]) for f in frames],
            "bass": [float(low[min(f, len(low) - 1)]) for f in frames]}


# ---------------------------------------------------------------------------
# Song structure (Structure \u25be): sections from repetition in the audio
# ---------------------------------------------------------------------------

def structure_available() -> bool:
    return beats_available()


def structure_features(filepath: str, progress_cb: ProgressCb = None) -> Dict[str, Any]:
    """Beats plus one feature vector per beat for find_sections(): chroma
    (harmony), MFCC (timbre) and loudness, each the median over the beat.
    Returns detect_beats()'s dict plus "features" (list of lists, one per
    beat) and "rms" (per beat). Slow-ish: a worker thread. Needs librosa."""
    if not structure_available():
        raise RuntimeError("librosa not installed")
    import librosa

    def report(msg):
        if progress_cb:
            progress_cb(msg)
    report("Decoding audio... (5%)")
    duration = None
    try:
        duration = librosa.get_duration(path=filepath)
    except Exception:
        pass
    y = _decode_16k_mono(filepath, 0.0, duration or 36000.0, sr=GENRE_SR)
    if len(y) == 0:
        raise RuntimeError("no audio decoded")
    sr, hop = GENRE_SR, 512
    report("Finding beats... (20%)")
    onset_env = librosa.onset.onset_strength(y=y, sr=sr, hop_length=hop)
    tempo, frames = librosa.beat.beat_track(onset_envelope=onset_env, sr=sr, hop_length=hop, units="frames")
    frames = np.asarray(frames, dtype=int)
    frames = frames[frames < len(onset_env)]
    if len(frames) < 8:
        raise RuntimeError("too few beats found for a structure analysis")
    report("Measuring harmony... (40%)")
    chroma = librosa.feature.chroma_cqt(y=y, sr=sr, hop_length=hop)
    report("Measuring timbre and loudness... (65%)")
    mfcc = librosa.feature.mfcc(y=y, sr=sr, hop_length=hop, n_mfcc=13)[1:]
    rms = librosa.feature.rms(y=y, hop_length=hop)
    spec = np.abs(librosa.stft(y, hop_length=hop))
    low = spec[librosa.fft_frequencies(sr=sr) < 150.0].sum(axis=0)
    n = min(chroma.shape[1], mfcc.shape[1], rms.shape[1])
    report("Summarizing per beat... (85%)")
    bounds = [int(f) for f in frames if f < n]
    sync = lambda m: librosa.util.sync(m[:, :n], bounds, aggregate=np.median)
    c_b, m_b, r_b = sync(chroma), sync(mfcc), sync(rms)
    # sync adds a segment before the first beat; drop it so row i = beat i
    k = len(bounds)
    c_b, m_b, r_b = c_b[:, -k:], m_b[:, -k:], r_b[:, -k:]
    feats = np.vstack([c_b, m_b / 20.0, r_b * 10.0]).T
    times = librosa.frames_to_time(np.asarray(bounds), sr=sr, hop_length=hop)
    return {"tempo": float(np.atleast_1d(tempo)[0]), "beats": [float(t) for t in times],
            "strength": [float(onset_env[f]) for f in bounds],
            "bass": [float(low[min(f, len(low) - 1)]) for f in bounds],
            "features": feats.tolist(), "rms": [float(v) for v in r_b[0]]}


def _novelty(sim, half):
    """Checkerboard-kernel novelty along the self-similarity diagonal
    (Foote): high where the music before and after a beat differ."""
    n = sim.shape[0]
    if half < 1 or n < 4:
        return np.zeros(n)
    idx = np.arange(-half, half)
    sign = np.where(idx < 0, -1.0, 1.0)
    taper = np.exp(-0.5 * ((idx + 0.5) / (half * 0.6)) ** 2)
    kernel = np.outer(sign, sign) * np.outer(taper, taper)
    padded = np.pad(sim, half, mode="edge")
    out = np.zeros(n)
    for i in range(n):
        block = padded[i:i + 2 * half, i:i + 2 * half]
        out[i] = float((block * kernel).sum())
    out[out < 0] = 0.0
    top = out.max()
    return out / top if top > 0 else out


REPEAT_RATIO = 0.6     # find_sections: how close a repeat must be (0..1, vs. self-similarity)


def find_sections(features, downbeats: List[int], min_beats: int = 16, max_sections: int = 24) -> Dict[str, Any]:
    """Section boundaries and repeat letters from per-beat features.

    features: one vector per beat. downbeats: beat indices where bars
    start (boundaries are only placed there). min_beats: shortest section.
    Returns {"bounds": [beat index, ...] (starts, first is 0, plus n at the
    end), "letters": ["A", "B", "A", ...] one per section,
    "novelty": [...]}. Pure numpy (no librosa)."""
    X = np.asarray(features, dtype=float)
    n = X.shape[0]
    if n < 4:
        return {"bounds": [0, n], "letters": ["A"], "novelty": [0.0] * n}
    X = (X - X.mean(axis=0)) / (X.std(axis=0) + 1e-9)
    X = X / (np.linalg.norm(X, axis=1, keepdims=True) + 1e-9)
    sim = X @ X.T
    half = int(max(2, min(16, min_beats // 2, n // 4)))
    nov = _novelty(sim, half)
    cands = sorted({d for d in downbeats if min_beats <= d <= n - min_beats})
    if not cands:
        cands = list(range(min_beats, n - min_beats + 1, max(1, min_beats // 2)))
    win = 1                       # a bar start takes the novelty right at it (+-1 beat)
    score = {d: float(nov[max(0, d - win):d + win + 1].max()) for d in cands}
    vals = np.array(list(score.values())) if score else np.zeros(1)
    thr = float(vals.mean() + 0.25 * vals.std()) if len(vals) > 2 else 0.0
    chosen: List[int] = []
    for d in sorted(cands, key=lambda c: -score[c]):
        if score[d] < thr or len(chosen) >= max_sections - 1:
            break
        if all(abs(d - c) >= min_beats for c in chosen):
            chosen.append(d)
    bounds = [0] + sorted(chosen) + [n]
    k = len(bounds) - 1
    # mean similarity between sections (block averages) -> repeat letters
    B = np.zeros((k, k))
    for a in range(k):
        for b in range(k):
            B[a, b] = sim[bounds[a]:bounds[a + 1], bounds[b]:bounds[b + 1]].mean()
    letters: List[str] = []
    if k == 1:
        letters = ["A"]
    else:
        # A repeat sounds about as much like the other section as each
        # section sounds like itself (its diagonal block); a chance
        # resemblance is far weaker than that.
        diag = np.diag(B)
        groups: List[List[int]] = []
        for i in range(k):
            best, best_g, ratio = None, None, 0.0
            for gi, members in enumerate(groups):
                v = float(np.mean([B[i, j] for j in members]))
                own = float(np.mean([diag[i]] + [diag[j] for j in members]))
                r = v / own if own > 1e-9 else 0.0
                if best is None or r > ratio:
                    best, best_g, ratio = v, gi, r
            if best is not None and ratio >= REPEAT_RATIO:
                groups[best_g].append(i)
                letters.append(chr(ord("A") + best_g) if best_g < 26 else f"S{best_g + 1}")
            else:
                groups.append([i])
                gi = len(groups) - 1
                letters.append(chr(ord("A") + gi) if gi < 26 else f"S{gi + 1}")
    return {"bounds": bounds, "letters": letters, "novelty": [float(v) for v in nov]}


def name_sections(letters: List[str], energy: List[float], vocal: Optional[List[Optional[float]]] = None
                  ) -> List[str]:
    """Guess section names from the repeat pattern (rule-based):
    the loudest repeated part -> Chorus; the most-repeated other part ->
    Verse; a part always right before a Chorus -> Pre-Chorus; a first /
    last part that doesn't come back -> Intro / Outro; other one-off parts
    -> Bridge, or Instrumental when (stems known) it has almost no vocals.
    Repeated names are numbered: Verse 1, Verse 2, ..."""
    k = len(letters)
    if k == 0:
        return []
    vocal = list(vocal) if vocal else [None] * k
    count = {L: letters.count(L) for L in letters}
    mean_e = {L: float(np.mean([energy[i] for i in range(k) if letters[i] == L])) for L in count}
    ends = letters[0] if (k >= 3 and letters[0] == letters[-1] and count[letters[0]] == 2) else None
    repeated = [L for L in count if count[L] >= 2 and L != ends]
    role: Dict[str, str] = {}
    if repeated:
        chorus = max(repeated, key=lambda L: (mean_e[L], count[L]))
        role[chorus] = "Chorus"
        rest = [L for L in repeated if L != chorus]
        if rest:
            verse = max(rest, key=lambda L: (count[L], -letters.index(L)))
            role[verse] = "Verse"
        for L in rest:
            if L in role:
                continue
            pos = [i for i in range(k) if letters[i] == L]
            if all(i + 1 < k and letters[i + 1] == chorus for i in pos):
                role[L] = "Pre-Chorus"
    # a part heard only at the very start and the very end: Intro / Outro
    bookend = ends
    names: List[str] = []
    for i, L in enumerate(letters):
        if L == bookend:
            names.append("Intro" if i == 0 else "Outro")
            continue
        if L in role:
            names.append(role[L])
            continue
        v = vocal[i]
        if i == 0 and count[L] == 1:
            names.append("Intro")
        elif i == k - 1 and count[L] == 1:
            names.append("Outro")
        elif count[L] == 1:
            names.append("Instrumental" if v is not None and v < 0.1 else "Bridge")
        else:
            names.append(f"Section {L}")
    totals = {nm: names.count(nm) for nm in names}
    seen: Dict[str, int] = {}
    out = []
    for nm in names:
        if totals[nm] > 1:
            seen[nm] = seen.get(nm, 0) + 1
            out.append(f"{nm} {seen[nm]}")
        else:
            out.append(nm)
    return out


def estimate_genre_mood(filepath: str, lyrics: str = "", progress_cb: ProgressCb = None) -> Dict[str, Any]:
    """Decode the whole file (mono, 22.05 kHz), measure the features with
    librosa, and score them. Slow-ish (seconds to a minute): run it in a
    worker thread. Raises if librosa isn't installed."""
    if not genre_mood_available():
        raise RuntimeError("librosa not installed (pip install librosa)")
    import librosa

    def report(msg):
        if progress_cb:
            progress_cb(msg)

    report("Decoding audio... (10%)")
    duration = None
    try:
        duration = librosa.get_duration(path=filepath)
    except Exception:
        pass
    y = _decode_16k_mono(filepath, 0.0, duration or 36000.0, sr=GENRE_SR)
    if len(y) == 0:
        raise RuntimeError("no audio decoded")
    sr = GENRE_SR
    hop = 1024 if available_ram_gb() < 5 else 512
    report("Measuring tempo... (35%)")
    tempo, _beats = librosa.beat.beat_track(y=y, sr=sr, hop_length=hop)
    tempo = float(np.atleast_1d(tempo)[0])
    report("Measuring spectrum... (60%)")
    features = {
        "tempo": tempo,
        "mean_rms": float(np.mean(librosa.feature.rms(y=y, hop_length=hop)[0])),
        "mean_cent": float(np.mean(librosa.feature.spectral_centroid(y=y, sr=sr, hop_length=hop)[0])),
        "mean_bw": float(np.mean(librosa.feature.spectral_bandwidth(y=y, sr=sr, hop_length=hop)[0])),
        "mean_contrast": float(np.mean(librosa.feature.spectral_contrast(y=y, sr=sr, hop_length=hop))),
        "mean_zcr": float(np.mean(librosa.feature.zero_crossing_rate(y, hop_length=hop)[0])),
        "percussiveness": float(np.mean(librosa.onset.onset_strength(y=y, sr=sr, hop_length=hop))),
    }
    report("Scoring... (95%)")
    result = score_genre_mood(features, lyrics)
    result["features"] = {k: round(v, 4) for k, v in features.items()}
    return result
