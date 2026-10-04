"""
timing_helpers.py -- generic (non-Tk) logic for waveform_tab.py.

Ported from the Sequence Editor project's media_utils.py, trimmed to what
waveform_tab.py actually needs and adapted to live inside trackED as a
*_tab.py plugin's helper module rather than a standalone app's data layer.
Nothing here imports tkinter or touches a GUI widget, so it can be used
(and unit-tested) independent of Tk, exactly like media_utils.py was.

Covers:
  - time formatting (format_time, format_time_ms)
  - waveform peak decoding via ffmpeg (or soundfile/miniaudio)
  - one combined per-file JSON cache, "<stem>-tracked.json" next to the
    media file: waveform peaks, stem regions, marks and tracks (see
    load_cache/update_cache) -- it travels with the media file rather
    than living in trackED's central session.json
  - overlap-lane assignment for drawing overlapping marks side by side
  - external timing-format exporters: xLights (.xtiming), LRC (.lrc),
    Audacity labels (.txt)
  - two playback engine wrappers behind one common interface: a
    SoundDevicePlaybackEngine (trackED's own approach -- numpy/soundfile/
    sounddevice, real audio output, no external binary) and an
    FfplayPlaybackEngine (the Sequence Editor's original approach --
    shells out to ffplay). SoundDevicePlaybackEngine is active by
    default; see ACTIVE_ENGINE below to switch, or fall back automatically
    if its packages aren't installed.

Optional third-party imports (numpy, soundfile, sounddevice) are probed
at import time and degrade gracefully -- see HAS_NUMPY / HAS_SOUNDFILE /
HAS_SOUNDDEVICE and PLAYBACK_MISSING below. waveform_tab.py uses those to
decide whether to show trackED's "missing packages -> offer to pip install"
UI (see its _show_missing_playback_ui), following the same pattern
audio_tab.py already uses for its own dependencies.
"""

from __future__ import annotations

import array
import json
import os
import re
import shutil
import struct
import copy
import subprocess
import threading
import xml.etree.ElementTree as ET
from typing import Callable, Any, Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# Optional third-party playback dependencies (probed once, degrade gracefully)
# ---------------------------------------------------------------------------
PLAYBACK_MISSING: Dict[str, str] = {}  # import_name -> pip package name, for whatever's absent

try:
    import numpy as np
except ImportError:
    np = None  # type: ignore
    PLAYBACK_MISSING["numpy"] = "numpy"

try:
    import soundfile as sf
except ImportError:
    sf = None  # type: ignore
    PLAYBACK_MISSING["soundfile"] = "soundfile"

try:
    import sounddevice as sd
except ImportError:
    sd = None  # type: ignore
    PLAYBACK_MISSING["sounddevice"] = "sounddevice"
except OSError:
    # sounddevice is installed but its native PortAudio library isn't found
    # on this system -- pip alone won't fix that, but we still want to
    # degrade gracefully rather than crash the whole plugin on import.
    sd = None  # type: ignore
    PLAYBACK_MISSING["sounddevice"] = "sounddevice"

HAS_NUMPY = np is not None
HAS_SOUNDFILE = sf is not None
HAS_SOUNDDEVICE = sd is not None

# ---------------------------------------------------------------------------
# Optional metadata / decode helpers (same ones the old audio_tab.py used).
# Neither is required if ffmpeg/ffprobe are on PATH, but without ffmpeg:
#   - tinytag supplies title/artist/album/etc. for the text panel, plus a
#     last-resort duration
#   - soundfile (above) or miniaudio decode the waveform peaks in-process
# ---------------------------------------------------------------------------
OPTIONAL_MISSING: Dict[str, str] = {}  # import_name -> pip package name

try:
    from tinytag import TinyTag
except ImportError:
    TinyTag = None  # type: ignore
    OPTIONAL_MISSING["tinytag"] = "tinytag"

try:
    import miniaudio
except ImportError:
    miniaudio = None  # type: ignore
    OPTIONAL_MISSING["miniaudio"] = "miniaudio"

HAS_TINYTAG = TinyTag is not None
HAS_MINIAUDIO = miniaudio is not None

# Formats each in-process decoder can handle (by extension). libsndfile
# >= 1.1 (bundled with soundfile >= 0.12 wheels) reads MP3; neither it nor
# miniaudio reads MP4/M4A, so .mp4 still needs ffmpeg for a waveform.
_SOUNDFILE_EXTS = {".wav", ".flac", ".ogg", ".aiff", ".aif", ".mp3"}
_MINIAUDIO_EXTS = {".wav", ".flac", ".ogg", ".mp3"}


# ---------------------------------------------------------------------------
# Built-in tag readers -- ported verbatim from the Sequence Editor's
# media_utils.py (this project's own code). Used when tinytag isn't
# installed or can't read a file.
# ---------------------------------------------------------------------------

ID3V1_GENRES = [
    "Blues", "Classic Rock", "Country", "Dance", "Disco", "Funk", "Grunge",
    "Hip-Hop", "Jazz", "Metal", "New Age", "Oldies", "Other", "Pop", "R&B",
    "Rap", "Reggae", "Rock", "Techno", "Industrial", "Alternative", "Ska",
    "Death Metal", "Pranks", "Soundtrack", "Euro-Techno", "Ambient",
    "Trip-Hop", "Vocal", "Jazz+Funk", "Fusion", "Trance", "Classical",
    "Instrumental", "Acid", "House", "Game", "Sound Clip", "Gospel",
    "Noise", "AlternRock", "Bass", "Soul", "Punk", "Space", "Meditative",
    "Instrumental Pop", "Instrumental Rock", "Ethnic", "Gothic", "Darkwave",
    "Techno-Industrial", "Electronic", "Pop-Folk", "Eurodance", "Dream",
    "Southern Rock", "Comedy", "Cult", "Gangsta", "Top 40", "Christian Rap",
    "Pop/Funk", "Jungle", "Native American", "Cabaret", "New Wave",
    "Psychedelic", "Rave", "Showtunes", "Trailer", "Lo-Fi", "Tribal",
    "Acid Punk", "Acid Jazz", "Polka", "Retro", "Musical", "Rock & Roll",
    "Hard Rock",
]


def _synchsafe_to_int(b):
    return (b[0] << 21) | (b[1] << 14) | (b[2] << 7) | b[3]


def _decode_id3_text(data):
    if not data:
        return ""
    enc = data[0]
    body = data[1:]
    try:
        if enc == 0:
            text = body.decode("latin-1", errors="replace")
        elif enc == 1:
            text = body.decode("utf-16", errors="replace")
        elif enc == 2:
            text = body.decode("utf-16-be", errors="replace")
        elif enc == 3:
            text = body.decode("utf-8", errors="replace")
        else:
            text = body.decode("latin-1", errors="replace")
    except Exception:
        text = ""
    return text.replace("\x00", "").strip()


def _parse_id3v2(path):
    """Parse ID3v2.3/2.4 tag frames from an MP3 file. Returns a dict of the
    common human-readable fields found; unrecognized frames are ignored."""
    tags = {}
    with open(path, "rb") as f:
        header = f.read(10)
        if len(header) < 10 or header[:3] != b"ID3":
            return tags
        version_major = header[3]
        tag_size = _synchsafe_to_int(header[6:10])
        body = f.read(tag_size)

    frame_map = {
        "TIT2": "title", "TPE1": "artist", "TALB": "album",
        "TYER": "year", "TDRC": "year", "TCON": "genre",
        "TRCK": "track_number", "COMM": "comment",
        "TPE2": "album_artist", "TCOM": "composer", "TPOS": "disc_number",
    }

    pos = 0
    while pos < len(body) - 10:
        frame_id = body[pos:pos + 4]
        if frame_id == b"\x00\x00\x00\x00":
            break
        try:
            frame_id_str = frame_id.decode("ascii")
        except UnicodeDecodeError:
            break
        if not frame_id_str.isalnum():
            break

        if version_major >= 4:
            frame_size = _synchsafe_to_int(body[pos + 4:pos + 8])
        else:
            frame_size = struct.unpack(">I", body[pos + 4:pos + 8])[0]

        frame_data = body[pos + 10:pos + 10 + frame_size]
        pos += 10 + frame_size
        if frame_size <= 0:
            continue

        key = frame_map.get(frame_id_str)
        if not key:
            continue

        if frame_id_str == "COMM" and len(frame_data) > 4:
            # encoding(1) + language(3) + short description + text; we skip
            # the language code and just decode encoding byte + remainder.
            value = _decode_id3_text(bytes([frame_data[0]]) + frame_data[4:])
        else:
            value = _decode_id3_text(frame_data)

        if value:
            tags[key] = value

    return tags


def _parse_id3v1(path):
    """Parse the legacy 128-byte ID3v1 tag at the end of an MP3 file, if any."""
    tags = {}
    size = os.path.getsize(path)
    if size < 128:
        return tags
    with open(path, "rb") as f:
        f.seek(size - 128)
        tag = f.read(128)
    if tag[:3] != b"TAG":
        return tags

    def field(b):
        return b.split(b"\x00")[0].decode("latin-1", errors="replace").strip()

    tags["title"] = field(tag[3:33])
    tags["artist"] = field(tag[33:63])
    tags["album"] = field(tag[63:93])
    tags["year"] = field(tag[93:97])
    tags["comment"] = field(tag[97:127])
    genre_code = tag[127]
    if genre_code < len(ID3V1_GENRES):
        tags["genre"] = ID3V1_GENRES[genre_code]
    return {k: v for k, v in tags.items() if v}


def extract_mp3_metadata(path):
    tags = {}
    try:
        tags.update(_parse_id3v1(path))  # baseline, may be overwritten below
        tags.update(_parse_id3v2(path))  # richer/preferred, takes priority
    except Exception as e:
        tags["error"] = str(e)
    tags["_file_size_bytes"] = os.path.getsize(path)
    return tags


def _read_atoms(f, end):
    """Read a sequence of MP4/QuickTime atoms (boxes) up to byte offset `end`.
    Returns a list of (type, start_offset, total_size, header_length)."""
    atoms = []
    while f.tell() < end:
        pos = f.tell()
        size_bytes = f.read(4)
        if len(size_bytes) < 4:
            break
        size = struct.unpack(">I", size_bytes)[0]
        atype_bytes = f.read(4)
        if len(atype_bytes) < 4:
            break
        atype = atype_bytes.decode("latin-1", errors="replace")
        header_len = 8
        if size == 1:
            large = f.read(8)
            if len(large) < 8:
                break
            size = struct.unpack(">Q", large)[0]
            header_len = 16
        elif size == 0:
            size = end - pos
        if size < header_len:
            break
        atoms.append((atype, pos, size, header_len))
        f.seek(pos + size)
    return atoms


_MP4_FIELD_MAP = {
    "\xa9nam": "title", "\xa9ART": "artist", "\xa9alb": "album",
    "\xa9day": "year", "\xa9gen": "genre", "\xa9too": "encoder",
    "\xa9wrt": "composer", "trkn": "track_number",
}


def extract_mp4_metadata(path):
    tags = {}
    try:
        with open(path, "rb") as f:
            file_size = os.path.getsize(path)
            top_atoms = _read_atoms(f, file_size)
            moov = next((a for a in top_atoms if a[0] == "moov"), None)
            if moov:
                _, mpos, msize, mhlen = moov
                f.seek(mpos + mhlen)
                moov_atoms = _read_atoms(f, mpos + msize)

                mvhd = next((a for a in moov_atoms if a[0] == "mvhd"), None)
                if mvhd:
                    _, vpos, vsize, vhlen = mvhd
                    f.seek(vpos + vhlen)
                    data = f.read(vsize - vhlen)
                    if data and data[0] == 1 and len(data) >= 32:
                        timescale = struct.unpack(">I", data[20:24])[0]
                        duration = struct.unpack(">Q", data[24:32])[0]
                    elif len(data) >= 20:
                        timescale = struct.unpack(">I", data[12:16])[0]
                        duration = struct.unpack(">I", data[16:20])[0]
                    else:
                        timescale = 0
                        duration = 0
                    if timescale:
                        tags["duration_seconds"] = round(duration / timescale, 2)

                udta = next((a for a in moov_atoms if a[0] == "udta"), None)
                if udta:
                    _, upos, usize, uhlen = udta
                    f.seek(upos + uhlen)
                    udta_atoms = _read_atoms(f, upos + usize)
                    meta = next((a for a in udta_atoms if a[0] == "meta"), None)
                    if meta:
                        _, mepos, mesize, mehlen = meta
                        f.seek(mepos + mehlen + 4)  # meta is a "full box": +4 version/flags
                        ilst = next(
                            (a for a in _read_atoms(f, mepos + mesize) if a[0] == "ilst"), None
                        )
                        if ilst:
                            _, ipos, isize, ihlen = ilst
                            f.seek(ipos + ihlen)
                            for atype, ap, asize, ahlen in _read_atoms(f, ipos + isize):
                                f.seek(ap + ahlen)
                                data_atom = next(
                                    (a for a in _read_atoms(f, ap + asize) if a[0] == "data"), None
                                )
                                if not data_atom:
                                    continue
                                _, dp, dsize, dhlen = data_atom
                                f.seek(dp + dhlen)
                                raw = f.read(dsize - dhlen)
                                if len(raw) < 8:
                                    continue
                                type_indicator = struct.unpack(">I", raw[0:4])[0]
                                payload = raw[8:]
                                key = _MP4_FIELD_MAP.get(atype, atype)
                                if type_indicator == 1:  # UTF-8 text
                                    tags[key] = payload.decode("utf-8", errors="replace").strip("\x00")
                                elif type_indicator in (13, 14):  # embedded cover art
                                    tags[key] = f"<embedded image, {len(payload)} bytes>"
                                elif key == "track_number" and len(payload) >= 4:
                                    tags[key] = str(struct.unpack(">H", payload[2:4])[0])
    except Exception as e:
        tags["error"] = str(e)
    tags["_file_size_bytes"] = os.path.getsize(path)
    return tags


def installable_missing() -> Dict[str, str]:
    """Everything worth offering to pip install: playback packages plus
    the optional metadata/decode ones."""
    out = dict(PLAYBACK_MISSING)
    out.update(OPTIONAL_MISSING)
    return out


def read_metadata(path: str) -> Optional[Dict[str, Any]]:
    """Tag/stream info for the text panel: TinyTag when installed (same
    fields the old audio_tab.py showed), else the built-in ID3/MP4 readers
    above (tags only -- no sample rate/bitrate, and duration only for MP4).
    Always returns a dict; "source" says which reader produced it, and
    "error" is set if neither could read the file."""
    tinytag_error = None
    if HAS_TINYTAG:
        try:
            tag = TinyTag.get(path)
            return {
                "source": "tinytag",
                "title": getattr(tag, "title", None),
                "artist": getattr(tag, "artist", None),
                "album": getattr(tag, "album", None),
                "duration": getattr(tag, "duration", None),
                "samplerate": getattr(tag, "samplerate", None),
                "channels": getattr(tag, "channels", None),
                "bitrate": getattr(tag, "bitrate", None),
            }
        except Exception as exc:
            tinytag_error = str(exc)
    ext = os.path.splitext(path)[1].lower()
    try:
        tags = extract_mp4_metadata(path) if ext in (".mp4", ".m4a") else extract_mp3_metadata(path)
    except Exception as exc:
        tags = {"error": str(exc)}
    out = {"source": "built-in"}
    for key in ("title", "artist", "album", "year", "genre", "track_number", "composer", "comment"):
        if tags.get(key):
            out[key] = tags[key]
    if tags.get("duration_seconds"):
        out["duration"] = float(tags["duration_seconds"])
    if tags.get("error") or tinytag_error:
        out["error"] = tags.get("error") or f"tinytag: {tinytag_error}"
    return out


def waveform_backend_for(path: str) -> Optional[str]:
    """Which decoder decode_waveform_peaks() will use for this file:
    "ffmpeg", "soundfile", "miniaudio", or None if none can."""
    ext = os.path.splitext(path)[1].lower()
    if find_ffmpeg():
        return "ffmpeg"
    if HAS_SOUNDFILE and ext in _SOUNDFILE_EXTS:
        if HAS_MINIAUDIO and ext in _MINIAUDIO_EXTS:
            return "soundfile (miniaudio fallback)"
        return "soundfile"
    if HAS_MINIAUDIO and ext in _MINIAUDIO_EXTS:
        return "miniaudio"
    return None


# ---------------------------------------------------------------------------
# Fallback cache/sidecar directory (used only when a media file's own
# directory isn't writable -- the normal case is a sidecar file right next
# to the media file, same convention as the Sequence Editor used).
# ---------------------------------------------------------------------------
_FALLBACK_DIR = os.path.join(os.path.expanduser("~"), ".waveform_tab_cache")


# ---------------------------------------------------------------------------
# Time formatting
# ---------------------------------------------------------------------------

def format_time(seconds: Optional[float]) -> str:
    if seconds is None:
        return "--:--"
    seconds = max(0, int(round(seconds)))
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def format_time_ms(seconds: Optional[float]) -> str:
    """Like format_time, but with millisecond precision -- used for the
    waveform panel's timestamps, where sub-second precision is genuinely
    useful for identifying a specific point in the audio."""
    if seconds is None:
        return "--:--.---"
    seconds = max(0.0, seconds)
    total_ms = int(round(seconds * 1000))
    h, rem_ms = divmod(total_ms, 3600000)
    m, rem_ms = divmod(rem_ms, 60000)
    s, ms = divmod(rem_ms, 1000)
    return f"{h}:{m:02d}:{s:02d}.{ms:03d}" if h else f"{m}:{s:02d}.{ms:03d}"


def parse_time(text: str) -> Optional[float]:
    """Parse "ss", "ss.mmm", "m:ss.mmm" or "h:mm:ss.mmm" (the formats
    format_time_ms produces, plus plain seconds). None if unparseable."""
    text = (text or "").strip()
    if not text:
        return None
    try:
        parts = [float(p) for p in text.split(":")]
    except ValueError:
        return None
    if len(parts) > 3 or any(p < 0 for p in parts):
        return None
    total = 0.0
    for p in parts:
        total = total * 60 + p
    return total


# ---------------------------------------------------------------------------
# Split / merge of timing marks (pure data -- used by waveform_tab.py and
# its timing panel; marks are the usual {"id","type","start","end",
# "label","track_id","source"} dicts)
# ---------------------------------------------------------------------------

MIN_RANGE = 0.01  # seconds; smallest range a split may produce


# ---------------------------------------------------------------------------
# How long words take to say/sing: a syllable-count heuristic (no
# dictionary download, no extra dependency). Used to split a range's time
# across its words in proportion to how long each takes, with short gaps
# after punctuation and at runs of whitespace / line breaks.
# ---------------------------------------------------------------------------

_VOWEL_GROUPS = re.compile(r"[aeiouy]+")
WORD_BASE_WEIGHT = 0.3        # every word takes some time (onset, consonants)
GAP_SENTENCE = 0.6            # after . ! ? (in syllable units)
GAP_CLAUSE = 0.35             # after , ; : and dashes
GAP_WHITESPACE = 0.35         # a run of 2+ spaces or a line break between words


def syllable_count(word: str) -> int:
    """English syllable estimate from vowel groups, with the usual fixes:
    silent final "e", "-le" endings, "-ed"/"-es" endings, and a few
    common diphthong splits. Non-English or odd tokens still get >= 1."""
    w = re.sub(r"[^a-z]", "", word.lower())
    if not w:
        return 1 if re.search(r"\d", word) else 0
    if len(w) <= 3:
        return 1
    count = len(_VOWEL_GROUPS.findall(w))
    if w.endswith("e") and not w.endswith(("le", "ee", "ye")) and count > 1:
        count -= 1                                  # silent e: "time", "love"
    elif w.endswith("le") and len(w) > 2 and w[-3] not in "aeiouy":
        pass                                        # "little", "table": the "-le" is its own syllable
    if w.endswith(("ed", "es")) and not w.endswith(("ted", "ded", "ses", "zes", "ches", "shes", "ges", "ces")) \
            and count > 1:
        count -= 1                                  # "played", "loves" (but "wanted", "kisses")
    count += len(re.findall(r"(ia|io|ua|eo|ium|iu)(?![aeiou])", w)) // 1 if count < 4 else 0
    return max(1, count)


def word_weight(word: str) -> float:
    """Relative time to sing a word (syllables plus a small base)."""
    syl = syllable_count(word)
    if syl == 0:           # a bare symbol like "&" or "-"
        return WORD_BASE_WEIGHT
    return WORD_BASE_WEIGHT + syl


# ---------------------------------------------------------------------------
# Inline per-word adjustments in lyric text
#
#   "beautiful {-1}"    one syllable fewer than the heuristic says
#   "fire {+1}"         one syllable more ("fi-er")
#   "love {+0.25s}"     a quarter second longer than its syllables give it
#   "oh {-120ms}"       120 ms shorter
#
# A {...} applies to the word just before it (with or without a space in
# between: "fire{+1}" works too). The two kinds can't be confused: a
# syllable adjustment is a whole number with no unit; a time adjustment
# always has a unit (s or ms). Anything else in braces ("{1.5}", "{x}",
# "{+1.5}") is just text. Several adjustments on one word add up. They
# stay in the card text (so they survive merging and re-splitting) but are
# left out of the waveform labels and of every export.
# ---------------------------------------------------------------------------

_ADJ_RE = re.compile(r"\{\s*([+-])\s*(\d+(?:\.\d*)?|\.\d+)\s*(ms|s)?\s*\}")


def _adjustment_matches(text: str) -> List[Tuple[int, int, str, float]]:
    """Valid adjustments in text: [(start, end, "syl"|"time", value), ...]
    (value: syllables, or seconds)."""
    out = []
    if "{" not in text:
        return out
    for m in _ADJ_RE.finditer(text):
        sign = -1.0 if m.group(1) == "-" else 1.0
        num, unit = m.group(2), m.group(3)
        if unit:
            value = float(num) / (1000.0 if unit == "ms" else 1.0)
            out.append((m.start(), m.end(), "time", sign * value))
        elif re.fullmatch(r"\d+", num):
            out.append((m.start(), m.end(), "syl", sign * int(num)))
        # a number with a decimal point but no unit is ambiguous: plain text
    return out


def strip_adjustments(text: str) -> str:
    """The text without its {+n} / {+n s} adjustments (nor the spaces or
    tabs just before them) -- what the waveform shows and exports write."""
    matches = _adjustment_matches(text)
    if not matches:
        return text
    out, pos = [], 0
    for a, b, _kind, _val in matches:
        out.append(text[pos:a].rstrip(" \t"))
        pos = b
    out.append(text[pos:])
    return "".join(out)


def word_infos(text: str) -> List[Dict[str, Any]]:
    """The words of a lyric text with their adjustments attached:
    [{"span": (a, b), "word": "fire", "base": 1, "syl_adj": 1,
      "syllables": 2, "time_adj": 0.0}, ...]. The span covers the word and
    the adjustments that follow it, so splitting a card into words keeps
    each word's adjustment with that word."""
    adjs = _adjustment_matches(text)
    masked = list(text)
    for a, b, _k, _v in adjs:
        for i in range(a, b):
            masked[i] = "\x00"       # one non-space run, even with spaces inside the braces
    infos: List[Dict[str, Any]] = []
    for m in re.finditer(r"\S+", "".join(masked)):
        a, b = m.start(), m.end()
        own = [(k, v) for x, y, k, v in adjs if a <= x and y <= b]
        clean = strip_adjustments(text[a:b])
        syl_adj = sum(v for k, v in own if k == "syl")
        time_adj = sum(v for k, v in own if k == "time")
        if not clean.strip() and own and infos:
            prev = infos[-1]           # "word {+1}": the braces belong to the word before
            prev["span"] = (prev["span"][0], b)
            prev["syl_adj"] += syl_adj
            prev["time_adj"] += time_adj
            continue
        infos.append({"span": (a, b), "word": clean, "syl_adj": syl_adj, "time_adj": time_adj})
    for info in infos:
        info["syl_adj"] = int(info["syl_adj"])
        info["base"] = syllable_count(info["word"]) if info["word"] else 0
        info["syllables"] = max(0, info["base"] + info["syl_adj"])
        info["time_adj"] = round(info["time_adj"], 6)
    return infos


def _info_weight(info: Dict[str, Any]) -> float:
    if not info["word"]:
        return 0.0
    return WORD_BASE_WEIGHT + info["syllables"]


def text_weight(text: str) -> float:
    """How much time a piece of lyric text is assumed to take: the sum of
    its word weights (syllables, including {+n} adjustments, plus a small
    base per word; spaces and punctuation don't count here)."""
    return sum(_info_weight(i) for i in word_infos(text))


def time_adjustment(text: str) -> float:
    """The sum of the text's {+n s} time adjustments, in seconds."""
    return sum(i["time_adj"] for i in word_infos(text))


def gap_weight(before: str, between: str) -> float:
    """Pause between two pieces: from punctuation at the end of `before`
    and the whitespace `between` them (2+ spaces or a line break)."""
    tail = strip_adjustments(before).rstrip()
    gap = 0.0
    if tail.endswith((".", "!", "?", "\u2026")):
        gap += GAP_SENTENCE
    elif tail.endswith((",", ";", ":", "-", "\u2013", "\u2014")):
        gap += GAP_CLAUSE
    if "\n" in between or len(between) >= 2:
        gap += GAP_WHITESPACE
    return gap


def split_text_at_fraction(text: str, frac: float) -> Tuple[str, str]:
    """Split text at the word boundary whose (syllable) weight share is
    closest to frac (0..1). Returns (left, right); either may be "" if the
    text has only one word."""
    infos = word_infos(text)
    if len(infos) < 2:
        return (text.strip(), "") if frac >= 0.5 else ("", text.strip())
    words = [text[i["span"][0]:i["span"][1]] for i in infos]
    weights = [_info_weight(i) for i in infos]
    total = sum(weights) or 1.0
    best_i, best_err, acc = 1, None, 0.0
    for i in range(1, len(words)):
        acc += weights[i - 1]
        err = abs(acc / total - frac)
        if best_err is None or err < best_err:
            best_i, best_err = i, err
    return " ".join(words[:best_i]), " ".join(words[best_i:])


def word_spans(text: str) -> List[Tuple[int, int]]:
    """(start, end) character spans of the words in text; punctuation
    stays attached to its word ("love," "don't"), and so does a following
    {+n} / {+n s} adjustment."""
    return [i["span"] for i in word_infos(text)]


def _timed_shares(start: float, end: float, weights: List[float], fixed: List[float],
                  gaps: List[float]) -> Optional[List[Tuple[float, float]]]:
    """Divide start..end among pieces: each gets its `fixed` seconds plus
    a share of the rest in proportion to its weight; gaps (weight units,
    one per piece, after it) are pauses between pieces. None if it
    doesn't fit."""
    total_w = sum(weights) + sum(gaps)
    spare = (end - start) - sum(fixed)
    if total_w <= 0 or spare <= 0:
        return None
    unit = spare / total_w
    out, t = [], start
    for w, f, g in zip(weights, fixed, gaps):
        s0, s1 = t, t + w * unit + f
        out.append((s0, s1))
        t = s1 + g * unit
    out[-1] = (out[-1][0], end)                  # absorb rounding
    if any(e - s < MIN_RANGE for s, e in out):
        return None
    return out


def plan_pieces(mark: Dict[str, Any], spans: List[Tuple[int, int]]) -> Optional[List[Tuple[float, Optional[float], str]]]:
    """Split a mark's label into the given character spans (in order,
    non-overlapping) and give each piece a share of the mark's time in
    proportion to its word weights -- plus/minus its {+n s} time
    adjustments -- leaving short gaps after punctuation and at 2+ spaces /
    line breaks. Returns [(start, end, text), ...] (end None for a point
    mark: all pieces keep its time), or None if it can't be done (fewer
    than 2 pieces, pieces too short, or time adjustments that don't fit)."""
    label = mark.get("label") or ""
    pieces = []
    for a, b in spans:
        text = label[a:b].strip()
        if not text:
            continue
        pieces.append([text, text_weight(text) or WORD_BASE_WEIGHT, a, b, time_adjustment(text)])
    if len(pieces) < 2:
        return None
    start = float(mark["start"])
    is_range = mark.get("type") == "range" and mark.get("end") is not None and mark["end"] > start
    if not is_range:
        return [(start, None, p[0]) for p in pieces]
    gaps = [gap_weight(label[p[2]:p[3]], label[p[3]:nxt[2]]) for p, nxt in zip(pieces, pieces[1:])] + [0.0]
    shares = _timed_shares(start, float(mark["end"]), [p[1] for p in pieces], [p[4] for p in pieces], gaps)
    if shares is None:
        return None
    return [(s0, s1, p[0]) for (s0, s1), p in zip(shares, pieces)]


def word_timings(mark: Dict[str, Any]) -> List[Dict[str, Any]]:
    """word_infos() of a mark's label, each with "seconds": how long the
    word would get if the card were split into words (None for a point
    mark, or when that split isn't possible)."""
    label = mark.get("label") or ""
    infos = word_infos(label)
    start = float(mark["start"])
    is_range = mark.get("type") == "range" and mark.get("end") is not None and mark["end"] > start
    secs: List[Optional[float]] = [None] * len(infos)
    if is_range and len(infos) == 1:
        secs = [float(mark["end"]) - start]
    elif is_range and infos:
        plan = plan_pieces(mark, [i["span"] for i in infos])
        if plan is not None and len(plan) == len(infos):
            secs = [e - s for s, e, _t in plan]
    for info, sec in zip(infos, secs):
        info["seconds"] = sec
    return infos


def format_adjust_seconds(value: float) -> str:
    """+0.25s / -0.12s (as written inside the braces)."""
    text = f"{abs(value):.3f}".rstrip("0").rstrip(".")
    return f"{'-' if value < 0 else '+'}{text}s"


def word_at(text: str, index: int) -> Optional[Dict[str, Any]]:
    """The word_infos() entry at a character index -- in the blank space
    after a word, that word (before the first word: the first word)."""
    infos = word_infos(text)
    best = None
    for info in infos:
        a, b = info["span"]
        if a <= index <= b:
            return info
        if b <= index:
            best = info
    return best if best is not None else (infos[0] if infos else None)


def adjust_word(text: str, index: int, syllables: int = 0, seconds: float = 0.0,
                clear: bool = False) -> Optional[Tuple[str, Tuple[int, int]]]:
    """Change the adjustment of the word at `index` (see word_at) by
    +/-syllables and/or +/-seconds, or remove it (clear=True). Rewrites
    that word's braces as "word {+1} {+0.1s}" (a part that comes to zero
    is dropped). Returns (new_text, (start, end) of the word) or None if
    there's no word there."""
    info = word_at(text, index)
    if info is None or not info["word"]:
        return None
    a, b = info["span"]
    syl = 0 if clear else int(info["syl_adj"] + syllables)
    secs = 0.0 if clear else round(info["time_adj"] + seconds, 3)
    if info["base"] + syl < 0:
        syl = -info["base"]          # not below zero syllables
    parts = [strip_adjustments(text[a:b]).rstrip()]
    if syl:
        parts.append(f"{{{'+' if syl > 0 else '-'}{abs(syl)}}}")
    if abs(secs) >= 0.0005:
        parts.append("{" + format_adjust_seconds(secs) + "}")
    word = " ".join(parts)
    return text[:a] + word + text[b:], (a, a + len(word))


def plan_split(mark: Dict[str, Any], at_time: Optional[float] = None,
               text_index: Optional[int] = None) -> Optional[Dict[str, Any]]:
    """Work out how to split one mark into two. Returns
    {"left": (start, end, label), "right": (start, end, label)} or None if
    it can't be split sensibly.

    - text_index strictly inside the label: split the text there, and for
      a range divide the time proportionally to each half's text_weight.
    - else at_time strictly inside a range: split the time there and the
      text proportionally (at the nearest word boundary).
    - else a range: split at the middle word boundary (by text weight),
      time proportional; with no text, split the time in half.
    Point marks (start == end) can only be split by text; both halves
    keep the same time."""
    label = mark.get("label") or ""
    start = float(mark["start"])
    is_range = mark.get("type") == "range" and mark.get("end") is not None and mark["end"] > start
    end = float(mark["end"]) if is_range else start

    left_text = right_text = None
    if text_index is not None and 0 < text_index < len(label):
        left_text, right_text = label[:text_index].strip(), label[text_index:].strip()
        if not left_text or not right_text:
            left_text = right_text = None
    if left_text is not None:
        if not is_range:
            return {"left": (start, None, left_text), "right": (start, None, right_text)}
        pieces = plan_pieces(mark, [(0, text_index), (text_index, len(label))])
        if pieces is None:
            return None
        (ls, le, lt), (rs, re_, rt) = pieces
        return {"left": (ls, le, lt), "right": (rs, re_, rt)}
    elif not is_range:
        return None
    elif at_time is not None and start + MIN_RANGE <= at_time <= end - MIN_RANGE:
        t = float(at_time)
        left_text, right_text = split_text_at_fraction(label, (t - start) / (end - start)) if label else ("", "")
    else:
        if label and len(word_infos(label)) >= 2:
            left_text, right_text = split_text_at_fraction(label, 0.5)
            wl, wr = text_weight(left_text), text_weight(right_text)
            shares = _timed_shares(start, end, [wl, wr], [time_adjustment(left_text), time_adjustment(right_text)],
                                   [0.0, 0.0])
            t = shares[0][1] if shares else start + (end - start) * wl / (wl + wr)
        else:
            left_text, right_text = label.strip(), ""
            t = (start + end) / 2
    if t - start < MIN_RANGE or end - t < MIN_RANGE:
        return None
    return {"left": (start, t, left_text), "right": (t, end, right_text)}


def neighbor_mark(marks: List[Dict[str, Any]], mark: Dict[str, Any], direction: int) -> Optional[Dict[str, Any]]:
    """The mark just before (-1) / after (+1) `mark` among marks with the
    same track_id, in time order."""
    group = sorted((m for m in marks if m.get("track_id") == mark.get("track_id")),
                   key=lambda m: (m["start"], m.get("end") or m["start"], m["id"]))
    ids = [m["id"] for m in group]
    if mark["id"] not in ids:
        return None
    j = ids.index(mark["id"]) + direction
    return group[j] if 0 <= j < len(group) else None


def merged_fields(a: Dict[str, Any], b: Dict[str, Any]) -> Tuple[float, float, str]:
    """(start, end, label) for merging two marks into one range: it spans
    both, and the labels are joined in time order."""
    first, second = (a, b) if (a["start"], a.get("end") or a["start"]) <= (b["start"], b.get("end") or b["start"]) else (b, a)
    start = min(first["start"], second["start"])
    end = max(first.get("end") or first["start"], second.get("end") or second["start"])
    label = " ".join(t for t in ((first.get("label") or "").strip(), (second.get("label") or "").strip()) if t)
    return start, end, label


# ---------------------------------------------------------------------------
# Reversible merges: a merged card remembers the cards it was made of
# (mark["pieces"]: their start/end/label/voices), so "Unmerge" can bring
# them back later -- not an undo: other edits may have happened since.
# ---------------------------------------------------------------------------

def _piece_of(m: Dict[str, Any]) -> Dict[str, Any]:
    p = {"start": m["start"], "end": m.get("end") if m.get("type") == "range" else None,
         "label": (m.get("label") or "").strip()}
    if m.get("voices"):
        p["voices"] = list(m["voices"])
    return p


def pieces_of(m: Dict[str, Any]) -> List[Dict[str, Any]]:
    """The original cards a mark stands for: its remembered pieces, or itself."""
    return [dict(p) for p in (m.get("pieces") or [])] or [_piece_of(m)]


def merged_pieces(a: Dict[str, Any], b: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Pieces of the card made by merging a and b (merges of merges keep
    all the original cards), in time order."""
    out = pieces_of(a) + pieces_of(b)
    out.sort(key=lambda p: (p["start"], p["end"] if p["end"] is not None else p["start"]))
    return out


def _piece_end(p):
    return p["end"] if p.get("end") is not None else p["start"]


def pieces_for_span(pieces: List[Dict[str, Any]], start: float, end: float) -> Optional[List[Dict[str, Any]]]:
    """After a merged card is split by hand: the pieces that belong to one
    part (start..end) -- a piece across the cut goes with the part holding
    its middle, trimmed to it. None when
    fewer than two are left (then there's nothing to unmerge)."""
    out = []
    for p in pieces:
        mid = (p["start"] + _piece_end(p)) / 2.0      # a piece across the cut goes with its larger part
        if start - 1e-6 <= mid < end + 1e-6 or (abs(mid - end) < 1e-6 and end == start):
            a, b = max(p["start"], start), min(_piece_end(p), end)
            q = dict(p)
            q["start"] = a
            if q.get("end") is not None:
                q["end"] = b
            out.append(q)
    return out if len(out) >= 2 else None


def unmerge_plan(mark: Dict[str, Any]) -> Tuple[List[Dict[str, Any]], str]:
    """The cards to restore from a merged card, and how exact that is:
      "exact"    -- nothing changed since the merge: the original cards
      "moved"    -- the card was moved/resized: the original boundaries,
                    scaled into its new span
      "text"     -- its text was edited: the new words are shared out in
                    the same numbers of words per card (or in proportion
                    when the count changed)
    Returns ([], "") when the mark isn't a merged card."""
    pieces = [dict(p) for p in (mark.get("pieces") or [])]
    if len(pieces) < 2:
        return [], ""
    how = []
    o0, o1 = pieces[0]["start"], max(_piece_end(p) for p in pieces)
    n0 = mark["start"]
    n1 = mark["end"] if mark.get("end") is not None else n0
    if abs(o0 - n0) > 1e-6 or abs(o1 - n1) > 1e-6:
        how.append("moved")
        # Stretch the original boundaries into the card's span -- unless the
        # card has (almost) no length any more (e.g. its End was cleared or
        # set onto its Start): then everything would land on one instant, so
        # keep the original lengths and only move them to the card's start.
        if o1 - o0 > 1e-9 and n1 - n0 >= MIN_RANGE * len(pieces):
            scale = (n1 - n0) / (o1 - o0)
        else:
            scale = 1.0

        def remap(t):
            return round(n0 + (t - o0) * scale, 6)
        for p in pieces:
            p["start"] = remap(p["start"])
            if p.get("end") is not None:
                p["end"] = remap(p["end"])
    current = (mark.get("label") or "").split()
    original = [(p.get("label") or "").split() for p in pieces]
    if current != [w for ws in original for w in ws]:
        how.append("text")
        counts = [len(ws) for ws in original]
        if sum(counts) != len(current):          # share out in proportion
            total = max(1, sum(counts))
            bounds, acc = [], 0
            for c in counts:
                acc += c
                bounds.append(round(acc * len(current) / total))
            counts = [b - a for a, b in zip([0] + bounds[:-1], bounds)]
        i = 0
        for p, c in zip(pieces, counts):
            p["label"] = " ".join(current[i:i + c])
            i += c
    return pieces, ("exact" if not how else "+".join(how))


# ---------------------------------------------------------------------------
# Importing timed text: LRC, Audacity labels, SRT -- or plain lyrics
# ---------------------------------------------------------------------------

_LRC_STAMP = re.compile(r"\[(\d+):(\d{1,2}(?:[.:]\d{1,3})?)\]")
_LRC_WORD_STAMP = re.compile(r"<\d+:\d{1,2}(?:[.:]\d{1,3})?>")
_SRT_TIME = re.compile(r"(\d+):(\d{2}):(\d{2})[,.](\d{1,3})\s*-->\s*(\d+):(\d{2}):(\d{2})[,.](\d{1,3})")


def _lrc_seconds(m, s):
    return int(m) * 60 + float(s.replace(":", "."))


def parse_timed_text(text: str, duration: Optional[float] = None) -> Tuple[str, List[Tuple[float, Optional[float], str]]]:
    """Recognize LRC ("[mm:ss.xx]line"), Audacity labels ("start<TAB>end<TAB>label")
    or SRT subtitles, and return (format, [(start, end, text), ...]).
    LRC lines run until the next stamp (the last one to `duration`);
    blank LRC lines just end the previous line. Anything else is
    ("plain", []) -- the caller keeps it as one block of lyrics."""
    lines = text.replace("\r\n", "\n").replace("\r", "\n").split("\n")

    # Audacity labels (spectral-selection lines starting with "\\" are skipped)
    aud = []
    for line in lines:
        if not line.strip() or line.startswith("\\"):
            continue
        parts = line.split("\t")
        try:
            a, b = float(parts[0]), float(parts[1])
        except (ValueError, IndexError):
            aud = None
            break
        aud.append((a, b if b > a else None, parts[2].strip() if len(parts) > 2 else ""))
    if aud:
        return "audacity", aud

    # SRT
    blocks, cur = [], None
    for line in lines:
        m = _SRT_TIME.search(line)
        if m:
            g = [int(x) for x in m.groups()[:3]] + [m.group(4)] + [int(x) for x in m.groups()[4:7]] + [m.group(8)]
            a = g[0] * 3600 + g[1] * 60 + g[2] + float("0." + g[3])
            b = g[4] * 3600 + g[5] * 60 + g[6] + float("0." + g[7])
            cur = [a, b, []]
            blocks.append(cur)
        elif cur is not None and line.strip() and not line.strip().isdigit():
            cur[2].append(line.strip())
    if blocks:
        return "srt", [(a, b, " ".join(t)) for a, b, t in blocks if t]

    # LRC
    offset = 0.0
    stamped = []
    for line in lines:
        mo = re.match(r"^\s*\[offset:\s*([+-]?\d+)\s*\]", line, re.I)
        if mo:
            offset = int(mo.group(1)) / 1000.0
            continue
        stamps = list(_LRC_STAMP.finditer(line))
        if not stamps or stamps[0].start() != len(line) - len(line.lstrip()):
            continue
        body = _LRC_WORD_STAMP.sub("", line[stamps[-1].end():]).strip()
        for st in stamps:
            stamped.append((max(0.0, _lrc_seconds(st.group(1), st.group(2)) - offset), body))
    if stamped:
        stamped.sort(key=lambda x: x[0])
        out = []
        for i, (t, body) in enumerate(stamped):
            if not body:
                continue
            nxt = stamped[i + 1][0] if i + 1 < len(stamped) else duration
            end = nxt if nxt is not None and nxt > t + MIN_RANGE else None
            out.append((t, end, body))
        return "lrc", out
    return "plain", []


def blend_color(hex_color: str, alpha: float, bg: str = "#1e1e1e") -> str:
    """Blend hex_color toward bg by alpha (0..1) and return a solid hex
    color. Tk canvas fills don't support real alpha, so translucency on
    the dark waveform background is faked this way: a low alpha reads as
    a dim, "translucent" band color, a high alpha reads as bright/opaque
    -- which is how track bands (dim) and the marks within them
    (brighter) are told apart."""
    hex_color = hex_color.lstrip("#")
    r, g, b = int(hex_color[0:2], 16), int(hex_color[2:4], 16), int(hex_color[4:6], 16)
    bg = bg.lstrip("#")
    br, bgc, bb = int(bg[0:2], 16), int(bg[2:4], 16), int(bg[4:6], 16)
    nr = int(r * alpha + br * (1 - alpha))
    ng = int(g * alpha + bgc * (1 - alpha))
    nb = int(b * alpha + bb * (1 - alpha))
    return f"#{nr:02x}{ng:02x}{nb:02x}"


# A 1-2-5 progression (like a ruler or graph-paper axis) so whatever interval
# gets picked reads as a "round" step at a glance, from milliseconds up to
# hours -- covers everything from fully zoomed in to a very long recording.
_TIME_GRID_CANDIDATES = (
    0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5,
    1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 900, 1800, 3600,
)


def time_grid_interval(view_span: float, target_lines: int = 8) -> float:
    """Pick a "nice" time interval (seconds) for vertical grid lines in
    the waveform so roughly `target_lines` lines fit across the current
    zoom level."""
    if view_span <= 0:
        return 1.0
    for candidate in _TIME_GRID_CANDIDATES:
        if view_span / candidate <= target_lines:
            return candidate
    return _TIME_GRID_CANDIDATES[-1]


def db_grid_step(amplitude_px: float) -> int:
    """Pick a "nice" dB step for horizontal amplitude grid lines based on
    how many vertical pixels are available."""
    if amplitude_px >= 300:
        return 1
    if amplitude_px >= 150:
        return 2
    if amplitude_px >= 80:
        return 3
    if amplitude_px >= 40:
        return 6
    return 10


# ---------------------------------------------------------------------------
# ffmpeg/ffprobe/ffplay discovery
# ---------------------------------------------------------------------------

def find_ffmpeg() -> Optional[str]:
    return shutil.which("ffmpeg")


def find_ffprobe() -> Optional[str]:
    return shutil.which("ffprobe")


def find_ffplay() -> Optional[str]:
    return shutil.which("ffplay")


# Why the most recent get_audio_duration_seconds() call's ffprobe/ffmpeg
# attempts failed (one entry per attempt), so the caller can log the real
# reason instead of guessing "not on PATH".
LAST_DURATION_ERRORS: List[str] = []


def _tail(text: Optional[str], n: int = 300) -> str:
    text = (text or "").strip()
    return text[-n:] if text else "(no output)"


def get_audio_duration_seconds(path: str) -> Optional[float]:
    """Best-effort duration lookup via ffprobe (preferred, exact) or by
    parsing ffmpeg's own stderr banner as a fallback. Returns None if
    neither tool is available or duration can't be determined."""
    LAST_DURATION_ERRORS.clear()
    ffprobe = find_ffprobe()
    if not ffprobe:
        LAST_DURATION_ERRORS.append("ffprobe: not found on PATH")
    else:
        try:
            proc = subprocess.run(
                [ffprobe, "-v", "error", "-show_entries", "format=duration",
                 "-of", "default=noprint_wrappers=1:nokey=1", path],
                capture_output=True, text=True, timeout=15,
            )
            value = proc.stdout.strip()
            try:
                if value:
                    return float(value)
            except ValueError:
                pass
            LAST_DURATION_ERRORS.append(
                f"ffprobe ({ffprobe}) exit {proc.returncode}, stdout={value!r}, stderr: {_tail(proc.stderr)}")
        except Exception as exc:
            LAST_DURATION_ERRORS.append(f"ffprobe ({ffprobe}): {type(exc).__name__}: {exc}")
    ffmpeg = find_ffmpeg()
    if not ffmpeg:
        LAST_DURATION_ERRORS.append("ffmpeg: not found on PATH")
    else:
        try:
            proc = subprocess.run([ffmpeg, "-i", path], capture_output=True, text=True, timeout=15)
            match = re.search(r"Duration:\s*(\d+):(\d+):(\d+\.\d+)", proc.stderr)
            if match:
                h, m, s = match.groups()
                return int(h) * 3600 + int(m) * 60 + float(s)
            LAST_DURATION_ERRORS.append(f"ffmpeg ({ffmpeg}): no Duration in banner: {_tail(proc.stderr)}")
        except Exception as exc:
            LAST_DURATION_ERRORS.append(f"ffmpeg ({ffmpeg}): {type(exc).__name__}: {exc}")
    # No ffmpeg: in-process sources, most exact first. soundfile/miniaudio
    # count actual frames; TinyTag estimates for VBR MP3s, so it's last --
    # the waveform is spread over this duration, so an estimate would skew
    # mark times slightly against real playback.
    ext = os.path.splitext(path)[1].lower()
    if HAS_SOUNDFILE and ext in _SOUNDFILE_EXTS:
        try:
            info = sf.info(path)
            if info.samplerate and info.frames > 0:
                return info.frames / float(info.samplerate)
        except Exception:
            pass
    if HAS_MINIAUDIO and ext in _MINIAUDIO_EXTS:
        try:
            info = miniaudio.get_file_info(path)
            if info.sample_rate and info.num_frames > 0:
                return info.num_frames / float(info.sample_rate)
        except Exception:
            pass
    meta = read_metadata(path)
    if meta and meta.get("duration"):
        return float(meta["duration"])
    return None


def decode_waveform_peaks(path: str, start_sec: float, duration_sec: float,
                           target_buckets: int, sample_rate: int = 22050) -> List[Tuple[float, float]]:
    """Min/max waveform peaks for [start_sec, start_sec+duration_sec).
    Uses ffmpeg when it's on PATH (any format, bounded memory); otherwise
    falls back to soundfile, then miniaudio (the old audio_tab.py's
    decoders). Returns [] if nothing can decode the file."""
    backend = waveform_backend_for(path)
    if backend == "ffmpeg":
        return _decode_peaks_ffmpeg(path, start_sec, duration_sec, target_buckets, sample_rate)
    if not duration_sec or duration_sec <= 0:
        return []
    target_buckets = max(20, min(4000, int(target_buckets)))
    ext = os.path.splitext(path)[1].lower()
    if HAS_SOUNDFILE and ext in _SOUNDFILE_EXTS:
        try:
            peaks = _decode_peaks_soundfile(path, start_sec, duration_sec, target_buckets)
            if peaks:
                return peaks
        except Exception:
            pass  # e.g. older libsndfile without MP3 support -> try miniaudio
    if HAS_MINIAUDIO and ext in _MINIAUDIO_EXTS:
        return _decode_peaks_miniaudio(path, start_sec, duration_sec, target_buckets, sample_rate)
    return []


class _PeakAccumulator:
    """Streams mono float samples in, emits (min, max) per bucket of
    `samples_per_bucket`, stopping at `target_buckets`. Uses numpy when
    available, else a pure-Python loop (same as the ffmpeg path)."""

    def __init__(self, samples_per_bucket: int, target_buckets: int):
        self.spb = max(1, int(samples_per_bucket))
        self.target = target_buckets
        self.peaks: List[Tuple[float, float]] = []
        self._carry = None  # numpy path
        self._cur_min, self._cur_max, self._count = 1.0, -1.0, 0  # pure-Python path

    @property
    def full(self) -> bool:
        return len(self.peaks) >= self.target

    def feed(self, mono) -> None:
        if self.full:
            return
        if HAS_NUMPY:
            data = np.asarray(mono, dtype=np.float32)
            if self._carry is not None and len(self._carry):
                data = np.concatenate((self._carry, data))
            n_full = min(len(data) // self.spb, self.target - len(self.peaks))
            if n_full > 0:
                blocks = data[: n_full * self.spb].reshape(n_full, self.spb)
                self.peaks.extend(zip(blocks.min(axis=1).tolist(), blocks.max(axis=1).tolist()))
            self._carry = data[n_full * self.spb:]
            return
        for v in mono:
            if v < self._cur_min:
                self._cur_min = v
            if v > self._cur_max:
                self._cur_max = v
            self._count += 1
            if self._count >= self.spb:
                self.peaks.append((self._cur_min, self._cur_max))
                self._cur_min, self._cur_max, self._count = 1.0, -1.0, 0
                if self.full:
                    return

    def finish(self) -> List[Tuple[float, float]]:
        if not self.full:
            if HAS_NUMPY:
                if self._carry is not None and len(self._carry):
                    self.peaks.append((float(self._carry.min()), float(self._carry.max())))
            elif self._count > 0:
                self.peaks.append((self._cur_min, self._cur_max))
        return self.peaks


def _decode_peaks_soundfile(path: str, start_sec: float, duration_sec: float,
                             target_buckets: int) -> List[Tuple[float, float]]:
    with sf.SoundFile(path) as f:
        sr = f.samplerate
        start_frame = max(0, int(start_sec * sr))
        total = max(1, int(duration_sec * sr))
        if start_frame:
            f.seek(start_frame)
        acc = _PeakAccumulator(total // target_buckets, target_buckets)
        remaining = total
        while remaining > 0 and not acc.full:
            block = f.read(min(65536, remaining), dtype="float32", always_2d=True)
            if len(block) == 0:
                break
            remaining -= len(block)
            acc.feed(block.mean(axis=1) if HAS_NUMPY else [sum(r) / len(r) for r in block])
        return acc.finish()


def _decode_peaks_miniaudio(path: str, start_sec: float, duration_sec: float,
                             target_buckets: int, sample_rate: int) -> List[Tuple[float, float]]:
    # Same call the old audio_tab.py used (explicit int sample rate --
    # 0/None doesn't work), resampled down to mono at `sample_rate`, which
    # is plenty for display and keeps the in-memory decode small.
    try:
        decoded = miniaudio.decode_file(path, nchannels=1, sample_rate=sample_rate)
    except Exception:
        return []
    samples = decoded.samples  # array.array("h"), mono
    sr = decoded.sample_rate or sample_rate
    a = max(0, int(start_sec * sr))
    b = min(len(samples), a + max(1, int(duration_sec * sr)))
    if b <= a:
        return []
    total = b - a
    acc = _PeakAccumulator(total // target_buckets, target_buckets)
    CHUNK = 65536
    for i in range(a, b, CHUNK):
        chunk = samples[i:min(b, i + CHUNK)]
        if HAS_NUMPY:
            acc.feed(np.frombuffer(chunk, dtype=np.int16).astype(np.float32) / 32768.0)
        else:
            acc.feed([v / 32768.0 for v in chunk])
        if acc.full:
            break
    return acc.finish()


def _decode_peaks_ffmpeg(path: str, start_sec: float, duration_sec: float,
                          target_buckets: int, sample_rate: int = 22050) -> List[Tuple[float, float]]:
    """Decode a time range [start_sec, start_sec+duration_sec) of the given
    media file into a coarse min/max waveform with `target_buckets` points.

    Streams ffmpeg's raw PCM output in fixed-size chunks and only retains
    the small downsampled peaks list -- never the full decoded audio -- so
    memory use stays bounded regardless of file length or zoom range. This
    is the Sequence Editor's original waveform *visualization* decode path,
    kept as-is: it only needs ffmpeg on PATH, independent of whichever
    playback engine is active (see ACTIVE_ENGINE below) -- so the waveform
    itself still renders even if numpy/soundfile/sounddevice aren't
    installed; only playback would be unavailable in that case.
    Returns a list of (min, max) float tuples in range [-1.0, 1.0], or an
    empty list if ffmpeg isn't available or the range is invalid.
    """
    ffmpeg = find_ffmpeg()
    if not ffmpeg or not duration_sec or duration_sec <= 0:
        return []

    target_buckets = max(20, min(4000, int(target_buckets)))
    total_samples = max(1, int(duration_sec * sample_rate))
    samples_per_bucket = max(1, total_samples // target_buckets)

    cmd = [
        ffmpeg, "-v", "error",
        "-ss", f"{max(0.0, start_sec):.3f}",
        "-t", f"{max(0.01, duration_sec):.3f}",
        "-i", path,
        "-f", "s16le", "-ac", "1", "-ar", str(sample_rate),
        "-",
    ]
    kwargs = {}
    if os.name == "nt":
        kwargs["creationflags"] = getattr(subprocess, "CREATE_NO_WINDOW", 0)

    peaks: List[Tuple[float, float]] = []
    cur_min, cur_max, count = 1.0, -1.0, 0
    leftover = b""
    CHUNK_BYTES = 65536  # ~32K samples per read -- keeps memory flat regardless of file size

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, **kwargs)
    try:
        while len(peaks) < target_buckets:
            chunk = proc.stdout.read(CHUNK_BYTES)
            if not chunk:
                break
            data = leftover + chunk
            usable_len = len(data) - (len(data) % 2)
            leftover = data[usable_len:]
            samples = array.array("h")
            samples.frombytes(data[:usable_len])
            for s in samples:
                v = s / 32768.0
                if v < cur_min:
                    cur_min = v
                if v > cur_max:
                    cur_max = v
                count += 1
                if count >= samples_per_bucket:
                    peaks.append((cur_min, cur_max))
                    cur_min, cur_max, count = 1.0, -1.0, 0
                    if len(peaks) >= target_buckets:
                        break
    finally:
        try:
            proc.terminate()
        except Exception:
            pass
        try:
            proc.stdout.close()
        except Exception:
            pass
        try:
            proc.wait(timeout=5)
        except Exception:
            pass

    if count > 0 and len(peaks) < target_buckets:
        peaks.append((cur_min, cur_max))
    return peaks


def rebucket_peaks(full_peaks: List[Tuple[float, float]], start_frac: float,
                    end_frac: float, target_buckets: int) -> List[Tuple[float, float]]:
    """Derive a (possibly zoomed) peaks array covering the fractional time
    range [start_frac, end_frac) of `full_peaks`, resampled to roughly
    `target_buckets` points -- pure Python, no decoding involved. Used to
    serve zoom/pan from the cached overview instead of re-invoking ffmpeg."""
    n = len(full_peaks)
    if n == 0:
        return []
    start_idx = max(0, min(n, int(start_frac * n)))
    end_idx = max(start_idx + 1, min(n, int(end_frac * n)))
    sub = full_peaks[start_idx:end_idx]
    if not sub:
        return []
    if len(sub) <= target_buckets:
        return sub  # already coarser than requested; no more detail to derive
    out = []
    per = len(sub) / target_buckets
    for i in range(target_buckets):
        a = int(i * per)
        b = max(a + 1, int((i + 1) * per))
        b = min(len(sub), b)
        group = sub[a:b]
        if not group:
            continue
        out.append((min(p[0] for p in group), max(p[1] for p in group)))
    return out


# ---------------------------------------------------------------------------
# Per-file sidecar helpers (waveform cache, marks/tracks)
# ---------------------------------------------------------------------------

def _sidecar_path(media_path: str, suffix: str) -> str:
    """Where a sidecar file for this media file should live:
    "<stem><suffix>" ("song-tracked.json") next to the media file if that
    directory is writable, else in a fallback dir under the home directory
    (using a flattened/escaped absolute path so files from different
    directories can't collide)."""
    directory = os.path.dirname(media_path) or "."
    stem = os.path.splitext(os.path.basename(media_path))[0]
    if os.access(directory, os.W_OK):
        return os.path.join(directory, f"{stem}{suffix}")
    os.makedirs(_FALLBACK_DIR, exist_ok=True)
    safe = re.sub(r"[^A-Za-z0-9_.-]", "_", os.path.splitext(os.path.abspath(media_path))[0])
    return os.path.join(_FALLBACK_DIR, f"{safe}{suffix}")


# ---------------------------------------------------------------------------
# Combined per-file cache: "<stem>-tracked.json" next to the media file
# (the "-tracked" suffix says which app owns it).
#
#   {
#     "format": 2,
#     "source_mtime": ..., "source_size": ...,   # media file identity
#     "duration": ..., "peaks": [...],           # derived -- dropped if the media changes
#     "regions": [...],                          # derived (stem analysis) -- ditto
#     "genre_mood": {...},                       # derived -- dropped only if the media's
#                                                #   timestamp (mtime) changes
#     "marks": [...], "tracks": [...]            # user data -- ALWAYS kept
#   }
#
# Marks/tracks are deliberately NOT invalidated when the media file's
# mtime/size change: they're the user's own work, and re-copying/restoring
# an audio file shouldn't make them silently disappear. Only the derived
# data is recomputed.
#
# "song.mp3" and "song.wav" in one folder share "song-tracked.json" --
# accepted, since they're presumably the same audio.
# ---------------------------------------------------------------------------

CACHE_SUFFIX = "-tracked.json"
WAVEFORM_CACHE_RESOLUTION = 4000  # buckets in the cached full-file overview (as in media_utils.py)
CACHE_FORMAT = 2
_DERIVED_KEYS = ("duration", "peaks", "regions")   # dropped when the media's mtime or size changes
_MTIME_KEYS = ("genre_mood",)                     # dropped only when the media's mtime changes
_cache_lock = threading.RLock()


def backup_name(path: str, stamp: str) -> str:
    """"song-tracked.json" -> "song-tracked-20261003-141500.json"."""
    root, ext = os.path.splitext(path)
    return f"{root}-{stamp}{ext}"


def backup_sidecar(path: str, stamp: Optional[str] = None) -> Optional[str]:
    """Copy a sidecar file to "<name>-<YYYYmmdd-HHMMSS><ext>" next to it
    (song-tracked-20261003-141500.json) and delete its older backups --
    only one is kept. Returns the backup's path, or None when there's
    nothing to back up / it failed."""
    import glob
    import time as _time
    if not path or not os.path.isfile(path):
        return None
    stamp = stamp or _time.strftime("%Y%m%d-%H%M%S")
    dest = backup_name(path, stamp)
    try:
        shutil.copy2(path, dest)
    except OSError:
        return None
    root, ext = os.path.splitext(path)
    pattern = glob.escape(root) + "-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]-[0-9][0-9][0-9][0-9][0-9][0-9]" + glob.escape(ext)
    for old in glob.glob(pattern):
        if os.path.abspath(old) != os.path.abspath(dest):
            try:
                os.remove(old)
            except OSError:
                pass
    return dest


def cache_path(media_path: str) -> str:
    return _sidecar_path(media_path, CACHE_SUFFIX)


def _source_identity(media_path: str) -> Dict[str, Any]:
    try:
        return {"source_mtime": os.path.getmtime(media_path), "source_size": os.path.getsize(media_path)}
    except OSError:
        return {"source_mtime": None, "source_size": None}


def _read_json(path: str) -> Optional[Dict[str, Any]]:
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else None
    except Exception:
        return None


def _write_json_atomic(path: str, data: Dict[str, Any]) -> bool:
    try:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        tmp = f"{path}.tmp{os.getpid()}"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f)
        os.replace(tmp, path)
        return True
    except Exception:
        return False


def _drop_stale(data: Dict[str, Any], ident: Dict[str, Any]) -> None:
    """Remove derived sections that no longer match the media file."""
    if not data:
        return
    mtime_changed = data.get("source_mtime") != ident["source_mtime"]
    if mtime_changed or data.get("source_size") != ident["source_size"]:
        for key in _DERIVED_KEYS:
            data.pop(key, None)
    if mtime_changed:
        for key in _MTIME_KEYS:
            data.pop(key, None)


def load_cache(media_path: str) -> Dict[str, Any]:
    """The whole combined cache for this media file ({} if none), with
    derived sections stripped if the media file changed since they were
    computed."""
    with _cache_lock:
        path = cache_path(media_path)
        data = dict((_read_json(path) if os.path.exists(path) else None) or {})
        _drop_stale(data, _source_identity(media_path))
        return data


def update_cache(media_path: str, **sections: Any) -> bool:
    """Read-modify-write the combined cache, replacing just the given
    top-level sections (e.g. marks=..., tracks=... or peaks=...). Safe to
    call from the loader/analysis threads and the UI thread."""
    with _cache_lock:
        path = cache_path(media_path)
        data = (_read_json(path) if os.path.exists(path) else None) or {}
        ident = _source_identity(media_path)
        _drop_stale(data, ident)
        data.update(ident)
        data["format"] = CACHE_FORMAT
        data.update(sections)
        return _write_json_atomic(path, data)


def load_waveform_cache(media_path: str) -> Optional[Dict[str, Any]]:
    """{"duration":..., "peaks":[...]} if cached and current, else None."""
    data = load_cache(media_path)
    peaks = [tuple(p) for p in data.get("peaks", [])]
    duration = data.get("duration")
    if not peaks or not duration:
        return None
    return {"duration": duration, "peaks": peaks}


def save_waveform_cache(media_path: str, duration: float, peaks: List[Tuple[float, float]]) -> None:
    update_cache(media_path, duration=duration, peaks=[list(p) for p in peaks])


def load_regions(media_path: str) -> List[Dict[str, Any]]:
    return list(load_cache(media_path).get("regions", []))


def save_regions(media_path: str, regions: List[Dict[str, Any]]) -> None:
    update_cache(media_path, regions=regions)


def load_genre_mood(media_path: str) -> Optional[Dict[str, Any]]:
    """The cached genre/mood estimate, or None if there isn't a current one."""
    value = load_cache(media_path).get("genre_mood")
    return value if isinstance(value, dict) and value.get("genre") else None


def save_genre_mood(media_path: str, value: Dict[str, Any]) -> None:
    update_cache(media_path, genre_mood=value)


def load_voices(media_path: str) -> List[str]:
    """The user's voice names for this file (see waveform_tab voices)."""
    return [v for v in load_cache(media_path).get("voices", []) if isinstance(v, str) and v]


def load_marks(media_path: str) -> List[Dict[str, Any]]:
    return list(load_cache(media_path).get("marks", []))


def load_tracks(media_path: str) -> List[Dict[str, Any]]:
    return list(load_cache(media_path).get("tracks", []))


def save_marks(media_path: str, marks: List[Dict[str, Any]],
               tracks: Optional[List[Dict[str, Any]]] = None,
               voices: Optional[List[str]] = None) -> None:
    sections: Dict[str, Any] = {"marks": marks, "tracks": tracks or []}
    if voices is not None:
        sections["voices"] = list(voices)
    update_cache(media_path, **sections)


def in_parentheses(text: str, span: Tuple[int, int]) -> bool:
    """Is every non-space character of text[span] inside parentheses
    (the brackets themselves count as inside)? "(love you)" -> True for
    "(love", "you)" and the whole; "love (you)" -> False."""
    a, b = span
    depth, inside = 0, []
    for ch in text:
        if ch == "(":
            depth += 1
            inside.append(True)
        elif ch == ")":
            inside.append(depth > 0)
            depth = max(0, depth - 1)
        else:
            inside.append(depth > 0)
    chars = [i for i in range(max(0, a), min(b, len(text))) if not text[i].isspace()]
    return bool(chars) and all(inside[i] for i in chars)


def has_parentheses(text: str) -> bool:
    """Does the text have any lyrics inside parentheses?"""
    depth = 0
    for ch in text or "":
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
        elif depth > 0 and not ch.isspace():
            return True
    return False


def paren_voice_name(voices: Optional[List[str]]) -> str:
    """The voice for lyrics in parentheses on a card with these voices:
    one past its highest "voice N" (none -> the card counts as voice 1,
    so "voice 2")."""
    highest = 1
    for v in voices or []:
        m = re.fullmatch(r"voice\s*(\d+)", (v or "").strip(), re.IGNORECASE)
        if m:
            highest = max(highest, int(m.group(1)))
    return f"{VOICE_PREFIX}{highest + 1}"


ALL_VOICES_NAME = "All voices"   # a card with no voice set is sung by all voices
ANY_VOICE = "(every card)"        # voice_export_tracks: one track with every card


def effective_voices(mark: Dict[str, Any]) -> List[str]:
    """The voices a card is for: its own voices; with none set, the voice
    its lyrics imply when they're all in parentheses (backing vocals);
    otherwise [] -- meaning all voices."""
    voices = list(mark.get("voices") or [])
    if voices:
        return voices
    label = mark.get("label") or ""
    if label.strip() and in_parentheses(label, (0, len(label))):
        return [paren_voice_name([])]
    return []


def voices_in(marks: List[Dict[str, Any]], known: Optional[List[str]] = None) -> List[str]:
    """Voices the marks use, in the file's voice order (known) first."""
    used: List[str] = []
    for m in marks:
        for v in effective_voices(m):
            if v not in used:
                used.append(v)
    order = [v for v in (known or []) if v in used]
    return order + [v for v in used if v not in order]


def voice_export_tracks(track_name: str, marks: List[Dict[str, Any]], outputs: List[str],
                        all_voices_in_each: bool = True) -> List[Tuple[str, List[Dict[str, Any]]]]:
    """Timing tracks for "Export per voice": one (name, marks) per entry
    of outputs, in that order, empty ones left out.
      a voice name      -> "<track> - <voice>": cards for that voice, plus
                           the cards for all voices if all_voices_in_each
      ALL_VOICES_NAME   -> "<track> - All voices": only the all-voices cards
      ANY_VOICE         -> "<track>": every card"""
    out = []
    for want in outputs:
        if want == ANY_VOICE:
            picked, name = list(marks), track_name
        elif want == ALL_VOICES_NAME:
            picked, name = [m for m in marks if not effective_voices(m)], f"{track_name} - {ALL_VOICES_NAME}"
        else:
            picked = [m for m in marks if want in effective_voices(m)
                      or (all_voices_in_each and not effective_voices(m))]
            name = f"{track_name} - {want}"
        picked.sort(key=lambda m: (m["start"], m.get("end") or m["start"]))
        if picked:
            out.append((name, picked))
    return out


def overlap_count(marks: List[Dict[str, Any]]) -> int:
    """How many marks start before the previous one (in time order) ends --
    xLights timing tracks can't hold overlapping marks."""
    ordered = sorted(marks, key=lambda m: m["start"])
    n, end = 0, None
    for m in ordered:
        if end is not None and m["start"] < end - 1e-6:
            n += 1
        this_end = m["end"] if m.get("type") == "range" and m.get("end") is not None else m["start"]
        end = this_end if end is None else max(end, this_end)
    return n


def overlapping_ids(marks: List[Dict[str, Any]]) -> set:
    """Ids of marks whose time overlaps another mark's (ranges sharing
    time; a point inside a range; two points at the same time)."""
    spans = []
    for m in marks:
        end = m["end"] if m.get("type") == "range" and m.get("end") is not None else m["start"]
        spans.append((m["start"], end, m["id"]))
    spans.sort()
    out = set()
    reach_end, reach_id = None, None
    for start, end, mid in spans:
        if reach_end is not None and (start < reach_end - 1e-6 or
                                      (start == end and abs(start - reach_end) < 1e-6 and start <= reach_end)):
            out.add(mid)
            out.add(reach_id)
        if reach_end is None or end > reach_end:
            reach_end, reach_id = end, mid
    return out


def copy_marks(marks: List[Dict[str, Any]], track_id: Optional[str], new_id: Callable[[], str],
               offset: float = 0.0) -> List[Dict[str, Any]]:
    """Copies of marks (new ids) for track_id, shifted by offset seconds."""
    out = []
    for m in marks:
        c = copy.deepcopy(m)
        c["id"] = new_id()
        c["track_id"] = track_id
        c["start"] = m["start"] + offset
        if c.get("end") is not None:
            c["end"] = m["end"] + offset
        for p in c.get("pieces") or []:         # a merged card's originals move with it
            p["start"] = p["start"] + offset
            if p.get("end") is not None:
                p["end"] = p["end"] + offset
        out.append(c)
    return out


# ---------------------------------------------------------------------------
# Bars / beats (Beats \u25be menu). Beat times come from
# audio_analysis.detect_beats; everything here is pure.
# ---------------------------------------------------------------------------

def downbeat_phase(strength: List[float], bass: List[float], beats_per_bar: int) -> int:
    """Which beat (index mod beats_per_bar) most likely starts a bar: the
    phase whose beats carry the most bass + onset strength. A guess --
    the Bars/Beats tracks can be renumbered afterwards."""
    if beats_per_bar <= 1 or not strength:
        return 0

    def norm(v):
        top = max(v) if v and max(v) > 0 else 1.0
        return [x / top for x in v]
    s_n, b_n = norm(list(strength)), norm(list(bass or [0.0] * len(strength)))
    scores = []
    for p in range(beats_per_bar):
        idx = range(p, len(s_n), beats_per_bar)
        vals = [s_n[i] + 1.5 * (b_n[i] if i < len(b_n) else 0.0) for i in idx]
        scores.append(sum(vals) / len(vals) if vals else 0.0)
    return max(range(beats_per_bar), key=lambda p: scores[p])


def _beat_len(beats: List[float]) -> float:
    gaps = sorted(b - a for a, b in zip(beats, beats[1:]) if b > a)
    return gaps[len(gaps) // 2] if gaps else 0.5


def beat_marks(beats: List[float], start: float, end: float, beats_per_bar: int = 4, phase: int = 0,
               mode: str = "beats", which: int = 1) -> List[Dict[str, Any]]:
    """Timing marks (start, end, label) from beat times, for beats in
    [start, end):
      "beats" -- every beat, labeled with its number in the bar (1..N),
                 lasting until the next beat
      "beat"  -- only beat number `which` of each bar, one beat long
      "bars"  -- one mark per bar (from each beat 1), numbered 1, 2, 3...
                 from the first bar in the range, lasting the whole bar
    phase: index of a beat that is beat 1 (see downbeat_phase)."""
    beats = sorted(beats)
    if not beats:
        return []
    bpb = max(1, int(beats_per_bar))
    blen = _beat_len(beats)
    out: List[Dict[str, Any]] = []

    def number(i):
        return (i - phase) % bpb + 1

    def next_time(i, step=1):
        j = i + step
        if j < len(beats):
            return beats[j]
        return beats[i] + step * blen
    bar_no = 0
    for i, t in enumerate(beats):
        if t < start - 1e-9 or t >= end:
            continue
        n = number(i)
        if mode == "beats":
            out.append({"start": t, "end": min(next_time(i), end), "label": str(n)})
        elif mode == "beat":
            if n == which:
                out.append({"start": t, "end": min(next_time(i), end), "label": str(n)})
        elif mode == "bars":
            if n == 1:
                bar_no += 1
                out.append({"start": t, "end": min(next_time(i, bpb), end), "label": str(bar_no)})
    return [m for m in out if m["end"] - m["start"] > 1e-6]


def parse_interval(text: str) -> Optional[float]:
    """Metronome interval from what the user typed: "0.5", "0.5 s",
    "500 ms", "120 bpm" (a bare number above 10 counts as BPM).
    Seconds, or None if it can't be read / is out of range."""
    s = (text or "").strip().lower().replace(",", ".")
    m = re.fullmatch(r"([0-9]*\.?[0-9]+)\s*(bpm|ms|s|sec|seconds?)?", s)
    if not m:
        return None
    value, unit = float(m.group(1)), m.group(2)
    if unit == "bpm" or (unit is None and value > 10):
        seconds = 60.0 / value if value > 0 else 0.0
    elif unit == "ms":
        seconds = value / 1000.0
    else:
        seconds = value
    return seconds if 0.02 <= seconds <= 60.0 else None


def metronome_marks(start: float, end: float, interval: float,
                    beats_per_bar: int = 4) -> List[Dict[str, Any]]:
    """Evenly spaced ticks from start, labeled 1..beats_per_bar like
    beats, each lasting until the next tick."""
    out: List[Dict[str, Any]] = []
    if interval <= 0 or end <= start:
        return out
    n = 0
    while True:
        t = start + n * interval
        if t >= end - 1e-9:
            break
        out.append({"start": round(t, 6), "end": round(min(t + interval, end), 6),
                    "label": str(n % max(1, beats_per_bar) + 1)})
        n += 1
        if n > 200000:
            break
    return out


def numbering_cycle(labels: List[str]) -> Optional[int]:
    """How a track's numbers run: N when they count 1..N and start over
    (a Beats track), 0 when they just count up (Bars), None when the
    labels aren't all numbers."""
    try:
        nums = [int(x) for x in labels]
    except (TypeError, ValueError):
        return None
    if not nums:
        return None
    top = max(nums)
    cyclic = len(nums) > top and all(b == a % top + 1 for a, b in zip(nums, nums[1:]))
    if cyclic and top <= 16:
        return top
    return 0


def renumber_from(labels: List[str], index: int, first: int, cycle: int = 0) -> List[str]:
    """New labels: from position index on, count up from `first` (cycle >
    0: wrap after cycle, as beat numbers do). Earlier labels are kept."""
    out = list(labels)
    n = first
    for i in range(index, len(out)):
        out[i] = str(n)
        n += 1
        if cycle and n > cycle:
            n = 1
    return out


def unique_track_name(name: str, existing: List[str]) -> str:
    """name, or "name 2", "name 3"... if a track already has it."""
    if name not in existing:
        return name
    k = 2
    while f"{name} {k}" in existing:
        k += 1
    return f"{name} {k}"


def find_span(text: str, piece: str, start: int = 0) -> Optional[Tuple[int, int]]:
    """Where a piece of text (e.g. one half of a split) is in the whole."""
    piece = (piece or "").strip()
    if not piece:
        return None
    i = text.find(piece, max(0, start - 1))
    if i < 0:
        i = text.find(piece)
    return (i, i + len(piece)) if i >= 0 else None


# ---------------------------------------------------------------------------
# Voices: user-defined names ("Lead", "Harmony", "voice 3") that timing
# marks can be assigned to -- mark["voices"] = [...], any number of them.
# The names are kept per audio file (one list shared by all its tracks).
# ---------------------------------------------------------------------------

VOICE_PREFIX = "voice "


def next_voice_name(existing: List[str]) -> str:
    """"voice N", with N one past the highest "voice <number>" in use."""
    highest = 0
    for name in existing:
        m = re.fullmatch(r"voice\s*(\d+)", (name or "").strip(), re.IGNORECASE)
        if m:
            highest = max(highest, int(m.group(1)))
    return f"{VOICE_PREFIX}{highest + 1}"


def merge_voice_lists(*lists: Optional[List[str]]) -> List[str]:
    """Union of voice lists, in first-seen order."""
    out: List[str] = []
    for lst in lists:
        for v in lst or []:
            if v not in out:
                out.append(v)
    return out


# ---------------------------------------------------------------------------
# Audio edges: align a card's Start to the foot of the next rising edge
# (an onset) and its End to the bottom of the next falling edge (where the
# sound has died away). Works on a fine loudness envelope of a few seconds
# of audio (5 ms buckets), with thresholds relative to that stretch:
#   high = low + 50% of the range, low-armed = low + 25%;
#   the foot / bottom = the latest (rise) or earliest (fall) point within
#   10% of the range above the local minimum.
# ---------------------------------------------------------------------------

EDGE_BUCKET_SEC = 0.005      # envelope resolution
EDGE_WINDOW_SEC = 4.0        # audio decoded per look
EDGE_CONTEXT_SEC = 0.5       # of it, before the search point
EDGE_MAX_LOOKS = 6           # give up after ~20 s without an edge
EDGE_MIN_STEP = 0.02         # "next" edge: at least this far past the current time
EDGE_SMOOTH_BUCKETS = 4      # moving average (20 ms)
EDGE_MIN_SPAN = 0.01         # quieter differences than this (1% of full scale) aren't edges


def edge_envelope(peaks: List[Tuple[float, float]], smooth: int = EDGE_SMOOTH_BUCKETS) -> List[float]:
    """Loudness per bucket from (min, max) peaks: half the peak-to-peak,
    lightly smoothed."""
    raw = [max(0.0, (float(mx) - float(mn)) / 2.0) for mn, mx in peaks]
    if smooth <= 1 or len(raw) < smooth:
        return raw
    out, acc = [], 0.0
    for i, v in enumerate(raw):
        acc += v
        if i >= smooth:
            acc -= raw[i - smooth]
        out.append(acc / min(i + 1, smooth))
    return out


def _percentile(values: List[float], pct: float) -> float:
    s = sorted(values)
    if not s:
        return 0.0
    k = max(0, min(len(s) - 1, int(round(pct / 100.0 * (len(s) - 1)))))
    return s[k]


def edge_times(env: List[float], t0: float, bucket: float, kind: str) -> List[float]:
    """All edges in an envelope starting at time t0 (bucket seconds
    each), in time order: kind "rise" -> feet of rising edges, "fall" ->
    bottoms of falling edges."""
    n = len(env)
    if n < 3 or bucket <= 0:
        return []
    low, high = _percentile(env, 10), _percentile(env, 95)
    span = high - low
    if span < EDGE_MIN_SPAN:
        return []
    thr_hi, thr_lo, near = low + 0.5 * span, low + 0.25 * span, 0.1 * span
    when = lambda i: t0 + i * bucket
    out: List[float] = []
    if kind == "rise":
        armed_at = 0 if env[0] < thr_lo else None
        for i in range(1, n):
            if env[i] < thr_lo:
                if armed_at is None:
                    armed_at = i
            elif env[i] >= thr_hi and armed_at is not None:
                seg = range(armed_at, i + 1)
                floor = min(env[k] for k in seg)
                out.append(when(max(k for k in seg if env[k] <= floor + near)))
                armed_at = None
        return out
    if kind == "fall":
        loud = env[0] >= thr_hi
        i = 1
        while i < n:
            if env[i] >= thr_hi:
                loud = True
            elif loud and env[i] < thr_lo:
                j = i
                while j < n - 1 and env[j + 1] < thr_hi:     # the valley: until it gets loud again
                    j += 1
                floor = min(env[k] for k in range(i, j + 1))
                out.append(when(min(k for k in range(i, j + 1) if env[k] <= floor + near)))
                loud = False
                i = j
            i += 1
        return out
    raise ValueError(kind)


def find_edge(env: List[float], t0: float, bucket: float, after: float, kind: str) -> Optional[float]:
    """The next edge (see edge_times) at least EDGE_MIN_STEP after
    `after`, or None."""
    return next((t for t in edge_times(env, t0, bucket, kind) if t > after + EDGE_MIN_STEP), None)


def find_prev_edge(env: List[float], t0: float, bucket: float, before: float, kind: str) -> Optional[float]:
    """The previous edge (see edge_times) at least EDGE_MIN_STEP before
    `before`, or None."""
    earlier = [t for t in edge_times(env, t0, bucket, kind) if t < before - EDGE_MIN_STEP]
    return earlier[-1] if earlier else None


# ---------------------------------------------------------------------------
# Overlap-lane assignment (for drawing overlapping marks side by side)
# ---------------------------------------------------------------------------

def assign_lanes(items: List[Tuple[float, float, str]], epsilon: float = 0.0) -> Dict[str, int]:
    """Greedy interval-graph lane assignment (like overlapping clips in a
    video timeline): items is a list of (start, end, id) -- end may equal
    start for a point mark. Returns {id: lane_index}, with overlapping
    items never sharing a lane and non-overlapping items packed into as
    few lanes as possible. `epsilon` pads the required gap between items
    before they're allowed to share a lane, so near-touching points/edges
    still separate visually (otherwise their labels would collide even
    though the raw intervals don't technically overlap)."""
    order = sorted(items, key=lambda it: it[0])
    lane_end: List[float] = []  # lane_end[i] = the (unpadded) end time currently occupying lane i
    lanes: Dict[str, int] = {}
    for start, end, item_id in order:
        for i, occupied_until in enumerate(lane_end):
            if start >= occupied_until + epsilon:
                lane_end[i] = end
                lanes[item_id] = i
                break
        else:
            lane_end.append(end)
            lanes[item_id] = len(lane_end) - 1
    return lanes


# ---------------------------------------------------------------------------
# xLights timing export (.xtiming)
#
# Format confirmed against a real file exported directly from xLights
# 2025.13.1 -- always a <timings> root (even for one track), each
# <timing> carrying subType/SourceVersion attributes, and each <Effect>
# using lowercase starttime/endtime (no id/ref/protectionKeyType).
# ---------------------------------------------------------------------------

XLIGHTS_SOURCE_VERSION = "2025.13.1"


def _xlights_effect_element(mark: Dict[str, Any]) -> ET.Element:
    """One <Effect> entry for a single mark. xLights timing marks are
    always intervals (there's no "instant" marker concept), so a point
    mark gets a minimal 1ms width rather than being dropped or
    misrepresented as a longer range."""
    start_ms = int(round(mark["start"] * 1000))
    end = mark.get("end")
    end_ms = start_ms + 1 if end is None else max(start_ms + 1, int(round(end * 1000)))
    label = strip_adjustments(mark.get("label") or "") or format_time_ms(mark["start"])
    return ET.Element("Effect", {
        "label": label,
        "starttime": str(start_ms),
        "endtime": str(end_ms),
    })


def build_xlights_timing_element(track_name: str, marks: List[Dict[str, Any]]) -> ET.Element:
    """Build one <timing name="..."> xLights timing-track element from a
    list of mark dicts (start/end in seconds -- end=None for a point
    mark -- and label). Marks are written in start-time order."""
    timing_el = ET.Element("timing", {
        "name": track_name,
        "subType": "",
        "SourceVersion": XLIGHTS_SOURCE_VERSION,
    })
    layer_el = ET.SubElement(timing_el, "EffectLayer")
    for m in sorted(marks, key=lambda m: m["start"]):
        layer_el.append(_xlights_effect_element(m))
    return timing_el


def export_xlights_timing_file(path: str, tracks_with_marks: List[Tuple[str, List[Dict[str, Any]]]]) -> None:
    """Write one .xtiming file. tracks_with_marks is a list of
    (track_name, marks) pairs, each becoming one <timing> element,
    always wrapped in a <timings> root -- xLights uses that wrapper even
    for a single-track export."""
    root = ET.Element("timings")
    for name, marks in tracks_with_marks:
        root.append(build_xlights_timing_element(name, marks))
    tree = ET.ElementTree(root)
    try:
        ET.indent(tree, space="  ")  # pretty-print -- Python 3.9+; purely cosmetic, safe to skip
    except AttributeError:
        pass
    tree.write(path, encoding="UTF-8", xml_declaration=True)


# ---------------------------------------------------------------------------
# LRC (.lrc lyrics-timing) and Audacity label-track export
#
# Neither format has a native concept of multiple simultaneous timing
# tracks (LRC is one lyric timeline; an Audacity label file maps to one
# label track), so exporting more than one track at once merges them into
# a single chronological list, with each label prefixed by its track name
# to keep them distinguishable. A single-track export needs no prefix.
# ---------------------------------------------------------------------------

def _lrc_timestamp(seconds: float) -> str:
    total_cs = int(round(seconds * 100))
    m, rem_cs = divmod(total_cs, 6000)
    s, cs = divmod(rem_cs, 100)
    return f"{m:02d}:{s:02d}.{cs:02d}"


def _merge_tracks_chronologically(
    tracks_with_marks: List[Tuple[str, List[Dict[str, Any]]]]
) -> List[Tuple[str, Dict[str, Any]]]:
    """Flatten [(track_name, marks), ...] into a single list of
    (track_name, mark) pairs sorted by start time."""
    combined = [(name, m) for name, marks in tracks_with_marks for m in marks]
    combined.sort(key=lambda nm: nm[1]["start"])
    return combined


def export_lrc_file(path: str, tracks_with_marks: List[Tuple[str, List[Dict[str, Any]]]]) -> None:
    """Write one .lrc file. LRC only really supports point-in-time
    markers -- the next line's timestamp implicitly ends the previous
    one -- so a range mark's end time isn't represented, only its
    start."""
    multi = len(tracks_with_marks) > 1
    combined = _merge_tracks_chronologically(tracks_with_marks)
    header_names = ", ".join(name for name, _marks in tracks_with_marks)
    lines = [f"[ti:{header_names}]"]
    for name, m in combined:
        ts = _lrc_timestamp(m["start"])
        label = strip_adjustments(m.get("label") or "") or format_time_ms(m["start"])
        if multi:
            label = f"[{name}] {label}"
        lines.append(f"[{ts}]{label}")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def export_audacity_labels_file(path: str, tracks_with_marks: List[Tuple[str, List[Dict[str, Any]]]]) -> None:
    """Write one Audacity label-track file: tab-separated start/end/
    label, one per line, no header. A point mark is written with equal
    start/end times, which Audacity displays as a single point label
    rather than a region."""
    multi = len(tracks_with_marks) > 1
    combined = _merge_tracks_chronologically(tracks_with_marks)
    lines = []
    for name, m in combined:
        start = m["start"]
        end = m["end"] if m.get("end") is not None else start
        label = strip_adjustments(m.get("label") or "") or format_time_ms(start)
        if multi:
            label = f"[{name}] {label}"
        lines.append(f"{start:.6f}\t{end:.6f}\t{label}")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + ("\n" if lines else ""))


EXPORT_FORMATS = {
    ".xtiming": ("xLights Timing", export_xlights_timing_file),
    ".lrc": ("LRC Lyrics", export_lrc_file),
    ".txt": ("Audacity Labels", export_audacity_labels_file),
}


def export_timing_tracks(path: str, tracks_with_marks: List[Tuple[str, List[Dict[str, Any]]]]) -> None:
    """Dispatch to the right exporter based on the chosen path's
    extension. Defaults to xLights format for an unrecognized/missing
    extension."""
    ext = os.path.splitext(path)[1].lower()
    _label, exporter = EXPORT_FORMATS.get(ext, EXPORT_FORMATS[".xtiming"])
    exporter(path, tracks_with_marks)


# ---------------------------------------------------------------------------
# Playback engines
#
# waveform_tab.py's playback controls (Play/Pause/Stop/skip/speed) talk to
# whichever engine make_playback_engine() returns through this one
# interface; it never touches sounddevice or subprocess directly. All
# *position/elapsed-time tracking* is the caller's job (waveform_tab.py's
# WaveformController, ported from the Sequence Editor's own play-state
# machine) -- an engine's only job is "start/stop playing this segment of
# this file", which keeps both engines simple and interchangeable.
# ---------------------------------------------------------------------------

class PlaybackEngine:
    """Common interface both playback backends implement."""

    volume = 1.0  # 1.0 = as recorded; applied to the next play_segment()

    def set_volume(self, volume: float) -> None:
        self.volume = max(0.0, min(2.0, float(volume)))

    def load(self, media_path: str) -> bool:
        """Called once when a new file is opened/selected. Returns True
        if this engine is able to play the file at all."""
        raise NotImplementedError

    def play_segment(self, start: float, duration: Optional[float], speed: float) -> bool:
        """Start playing from `start` seconds for `duration` seconds
        (None = to the end of the loaded file) at `speed`x. Non-blocking.
        Returns True if playback actually started."""
        raise NotImplementedError

    def stop(self) -> None:
        """Stop playback immediately (used for Pause/Stop/seek -- both
        engines implement "pause" as stop-and-remember-position, handled
        by the caller; see waveform_tab.py)."""
        raise NotImplementedError

    def is_active(self) -> bool:
        """True while the current segment is still playing; False once
        it finishes on its own or after stop()."""
        raise NotImplementedError

    def close(self) -> None:
        """Release any resources (decoded audio, subprocess) when the
        tab closes or a different file is loaded."""
        pass

class SoundDevicePlaybackEngine(PlaybackEngine):
    """trackED's own approach (see audio_tab.py): soundfile decodes the
    whole file into memory once, sounddevice.play() outputs a sliced
    chunk. Speed is applied by simple nearest-neighbor resampling, which
    changes pitch along with tempo -- a real trade-off against
    FfplayPlaybackEngine's ffmpeg atempo filter, which time-stretches
    without changing pitch. In exchange, this engine needs no external
    ffplay/ffmpeg binary for playback (only the numpy/soundfile/
    sounddevice pip packages), and avoids the process-spawn latency of
    relaunching ffplay on every seek/pause/resume."""

    def __init__(self):
        self._data = None
        self._sr = None

    def load(self, media_path: str) -> bool:
        self._data = None
        self._sr = None
        if not (HAS_NUMPY and HAS_SOUNDDEVICE):
            return False
        data = sr = None
        if HAS_SOUNDFILE:
            try:
                data, sr = sf.read(media_path, dtype="float32", always_2d=True)
            except Exception:
                data = None
        if data is None and HAS_MINIAUDIO:
            # Same fallback the old audio_tab.py's _load_pcm had.
            try:
                decoded = miniaudio.decode_file(media_path)
                data = np.frombuffer(decoded.samples, dtype=np.int16).astype(np.float32) / 32768.0
                data = data.reshape(-1, max(1, decoded.nchannels))
                sr = decoded.sample_rate
            except Exception:
                data = None
        if data is None:
            return False
        self._data = data
        self._sr = sr
        return True

    def play_segment(self, start: float, duration: Optional[float], speed: float) -> bool:
        if not HAS_SOUNDDEVICE or self._data is None:
            return False
        sr = self._sr
        start_frame = max(0, int(start * sr))
        if duration is None:
            end_frame = len(self._data)
        else:
            end_frame = min(len(self._data), int((start + duration) * sr))
        if start_frame >= end_frame:
            return False
        chunk = self._data[start_frame:end_frame]
        if abs(speed - 1.0) > 1e-3 and HAS_NUMPY:
            new_len = max(1, int(len(chunk) / speed))
            idx = np.linspace(0, len(chunk) - 1, new_len).astype(int)
            chunk = chunk[idx]
        if abs(self.volume - 1.0) > 1e-3 and HAS_NUMPY:
            chunk = np.clip(chunk * self.volume, -1.0, 1.0).astype(np.float32)
        try:
            sd.stop()
            sd.play(chunk, sr, blocking=False)
        except Exception:
            return False
        return True

    def stop(self) -> None:
        if HAS_SOUNDDEVICE:
            try:
                sd.stop()
            except Exception:
                pass

    def is_active(self) -> bool:
        if not HAS_SOUNDDEVICE:
            return False
        try:
            stream = sd.get_stream()
            return stream is not None and getattr(stream, "active", False)
        except Exception:
            return False

    def close(self) -> None:
        self.stop()
        self._data = None
        self._sr = None


class FfplayPlaybackEngine(PlaybackEngine):
    """The Sequence Editor's original playback approach: shells out to
    ffplay (part of the ffmpeg toolchain already used for waveform
    decoding) for each segment, using its -af atempo filter for a true
    pitch-preserving time-stretch. Fully working and kept here for a
    future fallback -- e.g. a machine with ffmpeg on PATH but without
    the numpy/soundfile/sounddevice pip stack -- but it is NOT the
    active engine by default (see ACTIVE_ENGINE / make_playback_engine
    below): every seek, pause, or speed change kills and relaunches the
    ffplay process, which SoundDevicePlaybackEngine avoids."""

    def __init__(self):
        self._media_path: Optional[str] = None
        self._process = None

    def load(self, media_path: str) -> bool:
        self.close()
        self._media_path = media_path
        return find_ffplay() is not None

    def play_segment(self, start: float, duration: Optional[float], speed: float) -> bool:
        self.stop()
        if not self._media_path:
            return False
        ffplay_path = find_ffplay()
        if not ffplay_path:
            return False
        cmd = [ffplay_path, "-nodisp", "-autoexit", "-loglevel", "quiet"]
        if start:
            cmd += ["-ss", f"{start:.3f}"]
        if duration is not None:
            cmd += ["-t", f"{duration:.3f}"]
        filters = []
        if abs(speed - 1.0) > 1e-6:
            filters.append(f"atempo={speed:.4f}")
        if abs(self.volume - 1.0) > 1e-3:
            filters.append(f"volume={self.volume:.2f}")
        if filters:
            cmd += ["-af", ",".join(filters)]
        cmd.append(self._media_path)
        try:
            self._process = subprocess.Popen(
                cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, stdin=subprocess.DEVNULL,
            )
        except Exception:
            self._process = None
            return False
        return True

    def stop(self) -> None:
        if self._process is not None:
            try:
                self._process.terminate()
            except Exception:
                pass
            self._process = None

    def is_active(self) -> bool:
        return self._process is not None and self._process.poll() is None

    def close(self) -> None:
        self.stop()
        self._media_path = None


# above are 2 alternate implementations for PlaybackEngine
# SoundDevicePlaybackEngine is currently the preferred engine (more direct control)

# Which engine waveform_tab.py should use by default. "sounddevice" is
# trackED's own approach (per the task this file was written for); "ffplay"
# is the Sequence Editor's original approach, wrapped above and fully
# working, but disabled here -- flip this (or pass engine="ffplay" to
# make_playback_engine) to reactivate it.
ACTIVE_ENGINE = "sounddevice"


def make_playback_engine(engine: Optional[str] = None) -> PlaybackEngine:
    """Construct the requested playback engine ("sounddevice" or
    "ffplay"), defaulting to ACTIVE_ENGINE. Falls back to
    FfplayPlaybackEngine automatically if "sounddevice" is requested but
    its packages aren't installed and ffplay is available -- so playback
    still works out of the box on a machine that has ffmpeg but not the
    pip stack, without the caller needing to know why."""
    choice = engine or ACTIVE_ENGINE
    if choice == "sounddevice" and not (HAS_NUMPY and (HAS_SOUNDFILE or HAS_MINIAUDIO) and HAS_SOUNDDEVICE) \
            and find_ffplay():
        choice = "ffplay"
    if choice == "ffplay":
        return FfplayPlaybackEngine()
    return SoundDevicePlaybackEngine()
