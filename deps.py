"""trackED's optional dependencies -- one list, shared by the in-app
Install button (waveform_tab.py) and the launchers (trackED.sh /
trackED.cmd run `python deps.py --install-core`).

Pure Python, no Tk. Nothing here is imported at module load except the
standard library, so it is safe to use before anything is installed.

Licensing (see HANDOFF.md): every pip package listed is MIT/BSD/ISC/
Apache-style. ffmpeg is an external program, run as a separate process
and never linked, so its (L)GPL build license doesn't reach trackED.
"""

import importlib
import importlib.util
import os
import shutil
import subprocess
import sys
from typing import Callable, Dict, List, Optional, Tuple

LogCb = Optional[Callable[[str], None]]

# key: our name. pip: package to install (None for a program). imports:
# modules that must all be importable. core: installed by the launchers
# without asking per package (small); the rest are offered in the
# Install dialog only.
DEPENDENCIES: List[Dict] = [
    dict(key="numpy", pip="numpy", imports=("numpy",), core=True, size="~20 MB",
         purpose="audio processing (playback, stems, transcription)", license="BSD"),
    dict(key="soundfile", pip="soundfile", imports=("soundfile",), core=True, size="~5 MB",
         purpose="reading WAV/FLAC/MP3 and writing stem files",
         license="BSD (bundles LGPL libsndfile, loaded dynamically)"),
    dict(key="sounddevice", pip="sounddevice", imports=("sounddevice",), core=True, size="~1 MB",
         purpose="audio playback", license="MIT"),
    dict(key="miniaudio", pip="miniaudio", imports=("miniaudio",), core=True, size="~1 MB",
         purpose="MP3 decoding when ffmpeg/soundfile can't", license="MIT"),
    dict(key="tinytag", pip="tinytag", imports=("tinytag",), core=True, size="<1 MB",
         purpose="song title/artist/duration", license="MIT"),
    dict(key="tkinterdnd2", pip="tkinterdnd2", imports=("tkinterdnd2",), core=True, size="~1 MB",
         purpose="drag and drop files into the window", license="MIT"),
    dict(key="psutil", pip="psutil", imports=("psutil",), core=True, size="~1 MB",
         purpose="free-memory check (Whisper model size) and diagnostics", license="BSD"),
    dict(key="pillow", pip="pillow", imports=("PIL",), core=True, size="~5 MB",
         purpose="images: JPEG/BMP/WebP, smooth zoom, singing faces, pixel editor", license="HPND (permissive)"),
    dict(key="ffmpeg", pip=None, program="ffmpeg", core=False, size="~100 MB",
         purpose="decoding MP3/MP4, fast deep zoom, stems and transcription input",
         license="external program (not linked)"),
    dict(key="demucs", pip="demucs", imports=("demucs", "torch"), core=False,
         size="~2-3 GB (includes PyTorch)",
         purpose="Stems: vocal / instrumental separation", license="MIT (PyTorch: BSD)"),
    dict(key="faster-whisper", pip="faster-whisper", imports=("faster_whisper",), core=False,
         size="~150 MB + model download on first use",
         purpose="Transcribe: lyrics from the vocals", license="MIT"),
    dict(key="librosa", pip="librosa", imports=("librosa",), core=False, size="~60 MB",
         purpose="Mood (genre/mood) and Beats (bars/beats)", license="ISC"),
]

BY_KEY = {d["key"]: d for d in DEPENDENCIES}


def _importable(name: str) -> bool:
    try:
        return importlib.util.find_spec(name) is not None
    except (ImportError, ValueError):
        return False


def status(dep: Dict) -> Tuple[str, str]:
    """("ok" | "missing" | "broken", note). "broken" means installed but
    not usable for a reason pip can't fix (e.g. no PortAudio library)."""
    if dep.get("program"):
        return ("ok", "") if shutil.which(dep["program"]) else ("missing", "")
    if not all(_importable(m) for m in dep["imports"]):
        return "missing", ""
    if dep["key"] == "sounddevice":
        try:
            importlib.import_module("sounddevice")
        except OSError:
            return "broken", ("installed, but the PortAudio library is missing "
                              "(Linux: sudo apt install libportaudio2)")
        except Exception:
            return "missing", ""
    return "ok", ""


def missing(include_broken: bool = False) -> List[Dict]:
    """Dependencies that aren't installed (in DEPENDENCIES order)."""
    out = []
    for d in DEPENDENCIES:
        st, _note = status(d)
        if st == "missing" or (include_broken and st == "broken"):
            out.append(d)
    return out


def missing_summary() -> str:
    """"demucs (Stems), librosa (Mood)" -- short names for the text panel."""
    return ", ".join(d["key"] for d in missing())


def pip_args(packages: List[str]) -> List[str]:
    return [sys.executable, "-m", "pip", "install", "--upgrade", "--no-warn-script-location"] + list(packages)


def _which_pkg_manager() -> Optional[str]:
    for pm in ("apt-get", "dnf", "pacman", "zypper", "brew"):
        if shutil.which(pm):
            return pm
    return None


def program_install_command(dep: Dict) -> Tuple[Optional[List[str]], str]:
    """(command, manual_hint) for an external program. command is None when
    trackED can't run the install itself; manual_hint says what to do."""
    name = dep["program"]
    if sys.platform.startswith("win"):
        if shutil.which("winget"):
            return (["winget", "install", "-e", "--id", "Gyan.FFmpeg",
                     "--accept-source-agreements", "--accept-package-agreements"],
                    "winget install -e --id Gyan.FFmpeg")
        return None, "Install ffmpeg from https://ffmpeg.org/download.html and add its bin folder to PATH."
    pm = _which_pkg_manager()
    manual = {
        "apt-get": f"sudo apt-get install {name}",
        "dnf": f"sudo dnf install {name}",
        "pacman": f"sudo pacman -S {name}",
        "zypper": f"sudo zypper install {name}",
        "brew": f"brew install {name}",
    }.get(pm, f"install {name} with your system's package manager")
    if pm == "brew":
        return ["brew", "install", name], manual
    if pm and shutil.which("pkexec"):
        yes = {"apt-get": ["install", "-y"], "dnf": ["install", "-y"], "pacman": ["-S", "--noconfirm"],
               "zypper": ["--non-interactive", "install"]}[pm]
        return ["pkexec", pm] + yes + [name], manual       # pkexec shows a password prompt
    return None, manual


def _run(cmd: List[str], log: LogCb, timeout: int = 3600) -> Tuple[int, str]:
    """Run cmd, passing each output line to log; returns (code, tail)."""
    kwargs = {}
    if sys.platform.startswith("win"):
        kwargs["creationflags"] = getattr(subprocess, "CREATE_NO_WINDOW", 0)
    if log:
        log("$ " + " ".join(cmd))
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                stdin=subprocess.DEVNULL, text=True, errors="replace", **kwargs)
    except FileNotFoundError as exc:
        return 127, f"{cmd[0]}: not found ({exc})"
    tail: List[str] = []
    assert proc.stdout is not None
    for line in proc.stdout:
        line = line.rstrip()
        tail = (tail + [line])[-30:]
        if log and line:
            log(line)
    try:
        code = proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        return 124, "timed out"
    return code, "\n".join(tail)


def explain_pip_failure(tail: str) -> str:
    """A plain-language reason for a failed pip run, if we recognize it."""
    low = tail.lower()
    if "externally-managed-environment" in low or "externally managed" in low:
        return ("This Python is managed by the system, so pip won't install into it. Start trackED "
                "with trackED.sh (it sets up its own environment in ~/.tracked/venv), or run it "
                "from a virtual environment.")
    if "no module named pip" in low:
        return "pip is not installed for this Python (Linux: sudo apt install python3-pip)."
    if "could not find a version" in low or "no matching distribution" in low:
        return ("No installable version was found for this Python version or system. Python "
                f"{sys.version_info.major}.{sys.version_info.minor} may be too new for this package.")
    if "connection" in low or "network" in low or "temporary failure" in low:
        return "pip couldn't reach the internet (check the network connection or proxy)."
    return ""


def refresh_windows_path() -> None:
    """After winget installs a program, Windows has a new PATH in the
    registry, but this process (and anything it starts) still has the old
    one. Re-read it -- the same thing logging out and back in would do."""
    if not sys.platform.startswith("win"):
        return
    try:
        import winreg
        parts = []
        for root, sub in ((winreg.HKEY_LOCAL_MACHINE,
                           r"SYSTEM\CurrentControlSet\Control\Session Manager\Environment"),
                          (winreg.HKEY_CURRENT_USER, r"Environment")):
            try:
                with winreg.OpenKey(root, sub) as key:
                    value, _t = winreg.QueryValueEx(key, "Path")
                    parts.append(os.path.expandvars(value))
            except OSError:
                pass
        if parts:
            os.environ["PATH"] = os.pathsep.join(parts)
    except Exception:
        pass


def install(keys: List[str], log: LogCb = None,
            on_step: Optional[Callable[[str, str], None]] = None) -> Tuple[List[str], List[Tuple[str, str]]]:
    """Install these dependencies one at a time (so a window can show which
    one is being installed). on_step(key, "start" | "ok" | "failed") is
    called around each. Returns (installed_keys, [(key, error)])."""
    deps = [BY_KEY[k] for k in keys if k in BY_KEY]
    ok: List[str] = []
    failed: List[Tuple[str, str]] = []

    def step(key, state):
        if on_step:
            on_step(key, state)
    for d in deps:
        step(d["key"], "start")
        if d.get("pip"):
            code, tail = _run(pip_args([d["pip"]]), log)
            importlib.invalidate_caches()
            if code == 0:
                ok.append(d["key"])
            else:
                failed.append((d["key"], explain_pip_failure(tail) or f"pip failed (exit code {code}); see the log."))
        else:
            cmd, manual = program_install_command(d)
            if cmd is None:
                failed.append((d["key"], f"trackED can't install it here. Run: {manual}"))
            else:
                code, _tail = _run(cmd, log)
                refresh_windows_path()
                if code == 0 or shutil.which(d["program"]):
                    ok.append(d["key"])
                else:
                    failed.append((d["key"], f"the installer failed (exit code {code}). You can also run: {manual}"))
        step(d["key"], "ok" if d["key"] in ok else "failed")
    return ok, failed


def main(argv: List[str]) -> int:
    """Launcher helper:
        python deps.py --list           show what's installed
        python deps.py --install-core   install the missing small packages"""
    if "--list" in argv or len(argv) <= 1:
        for d in DEPENDENCIES:
            st, note = status(d)
            print(f"  {'ok     ' if st == 'ok' else st:8} {d['key']:15} {d['purpose']}"
                  + (f"  [{note}]" if note else "") + ("" if d["core"] else "  (optional)"))
        return 0
    if "--install-core" in argv:
        keys = [d["key"] for d in missing() if d["core"] and d.get("pip")]
        if not keys:
            print("Core packages: all present.")
            return 0
        print("Installing: " + ", ".join(keys))
        _ok, failed = install(keys, log=print)
        for key, why in failed:
            print(f"FAILED {key}: {why}")
        return 1 if failed else 0
    print(main.__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
