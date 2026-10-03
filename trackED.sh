#!/usr/bin/env bash
# trackED launcher / installer for Linux (and macOS).
#
#   ./trackED.sh [trackED options and files]
#
# First run: checks for Python 3 with Tk; if anything is missing it asks
# before installing it with the system package manager (sudo). Then it
# makes trackED's own Python environment in ~/.tracked/venv (so pip
# installs never touch the system Python -- newer distributions refuse
# that anyway), installs the small core packages, and starts trackED.
# Later runs just start trackED. The big optional packages (demucs,
# Whisper, librosa) are offered by the app's Install button.
#
#   TRACKED_VENV=/some/dir ./trackED.sh   use another environment folder
#   ./trackED.sh --reinstall              rebuild the environment

set -u
HERE="$(cd "$(dirname "$(readlink -f "$0" 2>/dev/null || echo "$0")")" && pwd)"
VENV="${TRACKED_VENV:-$HOME/.tracked/venv}"
PY="$VENV/bin/python"

ask() {   # ask "question" -> 0 for yes
    local reply
    read -r -p "$1 [y/N] " reply </dev/tty || return 1
    [[ "$reply" =~ ^[Yy] ]]
}

pkg_install() {   # pkg_install <apt names> <dnf names> <pacman names> <zypper names> <brew names>
    if command -v apt-get >/dev/null; then sudo apt-get update && sudo apt-get install -y $1
    elif command -v dnf >/dev/null; then sudo dnf install -y $2
    elif command -v pacman >/dev/null; then sudo pacman -S --needed --noconfirm $3
    elif command -v zypper >/dev/null; then sudo zypper --non-interactive install $4
    elif command -v brew >/dev/null; then brew install $5
    else
        echo "No supported package manager found. Please install: $1"
        return 1
    fi
}

find_python() {
    for p in python3 python; do
        if command -v "$p" >/dev/null && "$p" -c 'import sys; sys.exit(sys.version_info < (3, 8))' 2>/dev/null; then
            echo "$p"; return 0
        fi
    done
    return 1
}

if [[ "${1:-}" == "--reinstall" ]]; then
    shift
    rm -rf "$VENV"
fi

if [[ ! -x "$PY" ]]; then
    echo "trackED: first-time setup"
    SYSPY="$(find_python)"
    if [[ -z "$SYSPY" ]]; then
        if ask "Python 3 is not installed. Install it now (needs sudo)?"; then
            pkg_install "python3 python3-tk python3-venv python3-pip" "python3 python3-tkinter python3-pip" \
                        "python tk python-pip" "python3 python3-tk python3-pip" "python python-tk" || exit 1
            SYSPY="$(find_python)" || { echo "Python still not found."; exit 1; }
        else
            echo "trackED needs Python 3.8 or newer."; exit 1
        fi
    fi
    if ! "$SYSPY" -c 'import tkinter' 2>/dev/null; then
        if ask "Python's Tk support (tkinter) is missing. Install it now (needs sudo)?"; then
            pkg_install "python3-tk" "python3-tkinter" "tk" "python3-tk" "python-tk" || exit 1
        else
            echo "trackED needs tkinter."; exit 1
        fi
    fi
    if ! "$SYSPY" -m venv --help >/dev/null 2>&1 || ! "$SYSPY" -c 'import ensurepip' 2>/dev/null; then
        if ask "Python's venv module is missing. Install it now (needs sudo)?"; then
            VER="$("$SYSPY" -c 'import sys; print(f"{sys.version_info[0]}.{sys.version_info[1]}")')"
            pkg_install "python3-venv python$VER-venv" "python3" "python" "python3" "python" || exit 1
        else
            echo "trackED needs the venv module."; exit 1
        fi
    fi
    mkdir -p "$(dirname "$VENV")"
    echo "Creating trackED's Python environment in $VENV ..."
    "$SYSPY" -m venv "$VENV" || { echo "Could not create $VENV"; exit 1; }
    "$PY" -m pip install --upgrade pip >/dev/null 2>&1
    echo "Installing the core packages (about 30 MB) ..."
    "$PY" "$HERE/deps.py" --install-core || echo "Some core packages failed; the app's Install button can retry."
    if ! command -v ffmpeg >/dev/null; then
        if ask "ffmpeg (audio decoding; recommended) is not installed. Install it now (needs sudo)?"; then
            pkg_install ffmpeg ffmpeg ffmpeg ffmpeg ffmpeg
        fi
    fi
    if [[ "$(uname)" == "Linux" ]] && ! ldconfig -p 2>/dev/null | grep -q libportaudio; then
        if ask "The PortAudio library (needed for playback) is missing. Install it now (needs sudo)?"; then
            pkg_install libportaudio2 portaudio portaudio portaudio2 portaudio
        fi
    fi
    echo "Setup done. (Optional extras -- stems, transcription, mood -- are offered by the Install button.)"
fi

exec "$PY" "$HERE/tracked.py" "$@"
