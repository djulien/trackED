"""
waveform_tab.py -- waveform + timing-marks/tracks editor plugin for trackED.

Discovered automatically because this file matches *_tab.py (see
utils.discover_tab_plugins). Claims .mp3/.mp4/.wav and draws a waveform
with named point/range timing marks and named timing tracks into the
Canvas panel, with playback controls and Export Timing (xLights/LRC/
Audacity) in a right-click track menu.

Also (v1.1):
  - Stem analysis (audio_analysis.py): demucs vocal/instrumental stems cached
    next to the audio as <stem>-vocals.wav / <stem>-non_vocals.wav (the old
    audio_tab.py names), waveform colored green/blue/teal/gray for
    vocal/instrumental/mixed/silent, region counts in the text panel.
  - Transcribe: Whisper text for the vocal parts of the selected range,
    used as the range's label; model auto-picked from free RAM or chosen
    from the Transcribe ▾ menu (remembered as the "whisper_model" preference).
  - Timing panel (timing_panel.py): selecting a track, or a mark in one,
    shows its marks in the text panel with editable start/end/text,
    -/+/@ time buttons, Split (text-proportional) and Merge.
  - Ctrl+click places a time cursor; Shift+Play loops the selection.
  - Everything per-file lives in one "<stem>-tracked.json" (see
    timing_helpers.load_cache).

Ported from the Sequence Editor project's tabs.py (an earlier, standalone
multi-tab editor this session also worked on), adapted to trackED's
plugin/onload() contract and generic EditorTab (sash position, cursor/
selection state, and the text pane are all handled by editor_tab.py
itself -- this plugin only owns the canvas). Two things were deliberately
left out of this port:

  - The Sequence Editor's onload() *scripting* feature -- a small Python
    sandbox letting a saved script generate marks/tracks programmatically.
    That's a different, unrelated use of the name "onload" than trackED's
    own plugin-discovery onload() this file implements; to avoid any
    confusion between the two, and because it's excluded from this port,
    it now lives in repl-todo.py, disabled, for possible reactivation
    later.
  - Its own ffplay-based playback engine is not the *active* one here --
    per the task this file was written for, playback now goes through a
    port of trackED's own approach instead (see timing_helpers.py:
    SoundDevicePlaybackEngine). The ffplay engine is still fully wrapped
    and available (FfplayPlaybackEngine, same file) for a future fallback;
    flip timing_helpers.ACTIVE_ENGINE to switch.

Dependencies: the waveform is decoded with ffmpeg/ffprobe when they're on
PATH; otherwise in-process with soundfile (WAV/FLAC/OGG/AIFF, and MP3 with
libsndfile >= 1.1), falling back to miniaudio for MP3 -- the same decoders
the old audio_tab.py used. MP4 audio still needs ffmpeg. tinytag (also from
audio_tab.py) supplies the title/artist/album/etc. shown in the text panel.
Playback (sounddevice engine) needs numpy + sounddevice + soundfile or
miniaudio. Anything missing is listed in the text panel and offered via
the "Install missing packages" button; marks/tracks editing never
depends on it.

Integration note: utils.discover_tab_plugins() tries *_tab.py plugins in
alphabetical order and the first one whose onload() returns truthy claims
the file. The old audio_tab.py (which also claimed .mp3/.mp4/.wav) has
been retired as audio-oldtab.py, which no longer matches *_tab.py, so
this plugin now handles audio files.

Panel sizing: this plugin doesn't move the sash itself; it sets
tab.min_sash / tab.preferred_sash and editor_tab._restore_sash() applies
them (see WaveformController.min_panel_height).
"""

from __future__ import annotations

import bisect
import copy
import subprocess
import sys
import threading
import time
import uuid
from pathlib import Path
from typing import Optional

import re
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog, colorchooser, filedialog

from logview_tab import debug
from utils import MOD_HINT_COLORS, current_modifiers, crumb
from utils import (insert_styled_text, get_preference, set_preference, get_stem_min_seconds, get_autosave_seconds,
                   get_edge_lead_in, register_modifier_button, register_modifier_listener)

import timing_helpers as th
import audio_analysis as aa
import deps
from timing_panel import TimingPanel

VERSION = "1.1.0"

# Waveform colors by stem region (after demucs), as in the old audio_tab.py
REGION_COLORS = {             # defaults; customizable (click the color key under the waveform)
    "vocal": "#229954",       # green  - vocal-only (a darker green, to stand apart from teal)
    "novocal": "#3498db",     # blue   - instrumental-only
    "mixed": "#1abc9c",       # teal   - both
    "silent": "#6b6b6b",      # gray   - neither (the old tab counted this as "mixed")
}
STEM_LABELS = {"vocal": "vocal", "novocal": "instrumental", "mixed": "mixed", "silent": "silent"}


def stem_colors():
    """The stem colors in use: the "stem_colors" preference over the defaults."""
    colors = dict(REGION_COLORS)
    saved = get_preference("stem_colors", {}) or {}
    if isinstance(saved, dict):
        for kind, color in saved.items():
            if kind in colors and isinstance(color, str) and re.match(r"^#[0-9a-fA-F]{6}$", color):
                colors[kind] = color
    return colors
WAVE_COLOR = "#4fc3f7"     # before/without stem analysis
CURSOR_COLOR = "#e0e0e0"
CURSOR_PLAY_COLOR = "#ffffff"   # the @cursor while playing (not red: red is a point mark)
SHIFT_MASK = 0x0001
CONTROL_MASK = 0x0004
AUDIO_EXTS = {".mp3", ".mp4", ".wav"}
FILE_TYPES = [("Audio", " ".join(f"*{e}" for e in sorted(AUDIO_EXTS)))]   # File > Open (tracked.py)


# ---------------------------------------------------------------------------
# Small UI helpers (ported as-is from the Sequence Editor)
# ---------------------------------------------------------------------------

class StemColorPicker:
    """A small non-native color picker: hue / saturation / brightness
    sliders, a hex field and a swatch. Every change calls on_change(color)
    right away (live preview); OK calls on_done(color), Cancel/close calls
    on_done(None). Explicit colors, so it's readable on dark themes too."""

    BG, FG = "#f2f2f2", "#1e1e1e"

    def __init__(self, parent, title, color, on_change, on_done):
        import colorsys
        self._colorsys = colorsys
        self.on_change, self.on_done = on_change, on_done
        self.color = color
        self._done = False
        h, s, v = self._hex_to_hsv(color)
        self.top = tk.Toplevel(parent)
        self.top.title(title)
        self.top.configure(bg=self.BG)
        try:
            self.top.transient(parent.winfo_toplevel())
        except tk.TclError:
            pass
        self.swatch = tk.Frame(self.top, width=220, height=36, bg=color, relief="solid", bd=1)
        self.swatch.pack(padx=12, pady=(12, 6), fill="x")
        self.scales = {}
        for key, label, top, value in (("h", "Hue", 360, h * 360), ("s", "Saturation", 100, s * 100),
                                       ("v", "Brightness", 100, v * 100)):
            sc = tk.Scale(self.top, label=label, from_=0, to=top, orient="horizontal", length=240,
                          bg=self.BG, fg=self.FG, troughcolor="#d0d0d0", highlightthickness=0,
                          command=lambda _v: self._from_sliders())
            sc.set(round(value))
            sc.pack(padx=12, fill="x")
            self.scales[key] = sc
        row = tk.Frame(self.top, bg=self.BG)
        row.pack(padx=12, pady=8, fill="x")
        tk.Label(row, text="Hex", bg=self.BG, fg=self.FG).pack(side="left")
        self.hex_entry = tk.Entry(row, width=9, bg="#ffffff", fg=self.FG, insertbackground=self.FG)
        self.hex_entry.pack(side="left", padx=(4, 10))
        self.hex_entry.insert(0, color)
        self.hex_entry.bind("<Return>", lambda e: self._from_hex())
        for text, cmd in (("Cancel", self.cancel), ("OK", self.ok)):
            tk.Button(row, text=text, command=cmd, bg="#e2e2e2", fg=self.FG, activebackground="#cfe0ff",
                      activeforeground=self.FG, cursor="hand2", padx=10).pack(side="right", padx=(6, 0))
        self.top.protocol("WM_DELETE_WINDOW", self.cancel)
        self.top.bind("<Escape>", lambda e: self.cancel())

    def _hex_to_hsv(self, color):
        try:
            r, g, b = (int(color[i:i + 2], 16) / 255.0 for i in (1, 3, 5))
        except (ValueError, IndexError, TypeError):
            r = g = b = 0.5
        return self._colorsys.rgb_to_hsv(r, g, b)

    def set_hsv(self, h, s, v):
        """h in 0..360, s and v in 0..100 (what the sliders show)."""
        for key, val in (("h", h), ("s", s), ("v", v)):
            self.scales[key].set(val)
        self._from_sliders()

    def _from_sliders(self):
        try:
            h, s, v = (float(self.scales[k].get()) for k in ("h", "s", "v"))
        except (tk.TclError, ValueError):
            return
        r, g, b = self._colorsys.hsv_to_rgb((h % 360) / 360.0, s / 100.0, v / 100.0)
        self._apply("#%02x%02x%02x" % (round(r * 255), round(g * 255), round(b * 255)), update_hex=True)

    def _from_hex(self):
        text = self.hex_entry.get().strip()
        if not text.startswith("#"):
            text = "#" + text
        if re.match(r"^#[0-9a-fA-F]{6}$", text):
            h, s, v = self._hex_to_hsv(text)
            for key, val in (("h", h * 360), ("s", s * 100), ("v", v * 100)):
                self.scales[key].set(round(val))
            self._apply(text.lower(), update_hex=False)

    def _apply(self, color, update_hex):
        if color == self.color and not update_hex:
            return
        self.color = color
        try:
            self.swatch.configure(bg=color)
            if update_hex and self.hex_entry.get() != color:
                self.hex_entry.delete(0, "end")
                self.hex_entry.insert(0, color)
        except tk.TclError:
            pass
        self.on_change(color)

    def ok(self):
        self._close(self.color)

    def cancel(self):
        self._close(None)

    def _close(self, result):
        if self._done:
            return
        self._done = True
        try:
            self.top.destroy()
        except tk.TclError:
            pass
        self.on_done(result)


class _Tooltip:
    """A small delayed tooltip for a toolbar button/control."""

    def __init__(self, widget, text: str, delay_ms: int = 500):
        self.widget = widget
        self.text = text
        self.delay_ms = delay_ms
        self._after_id = None
        self._tip = None
        widget.bind("<Enter>", self._schedule, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonPress>", self._hide, add="+")
        widget.bind("<ButtonRelease>", self._hide, add="+")

    def _schedule(self, event=None):
        # Cancel a pending show first: two Enters in a row (X11 sends one
        # when a menubutton's menu takes the grab) used to leave an
        # uncancellable timer that showed the tip over the open menu.
        self._cancel()
        if self._grabbed():
            return
        self._after_id = self.widget.after(self.delay_ms, self._show)

    def _cancel(self):
        if self._after_id is not None:
            try:
                self.widget.after_cancel(self._after_id)
            except Exception:
                pass
            self._after_id = None

    def _grabbed(self):
        """True while a menu is posted (or a drag holds the mouse): the tip
        would cover the menu and swallow clicks on its first entries."""
        try:
            return bool(self.widget.grab_current())
        except Exception:
            return False

    def _show(self):
        self._after_id = None
        if self._tip is not None or self._grabbed():
            return
        try:
            under = self.widget.winfo_containing(*self.widget.winfo_pointerxy())
        except Exception:
            under = None
        if under is not None and under is not self.widget:
            return                      # the pointer has moved on (e.g. into the menu)
        x = self.widget.winfo_rootx() + 10
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
        self._tip = tk.Toplevel(self.widget)
        self._tip.wm_overrideredirect(True)
        self._tip.wm_geometry(f"+{x}+{y}")
        # Explicit foreground too: on a dark desktop theme Tk's default text
        # color is light, which vanished on this light background.
        tk.Label(
            self._tip, text=self.text, background="#ffffe0", foreground="#1e1e1e",
            relief="solid", borderwidth=1, justify="left",
            font=("TkDefaultFont", 8), padx=4, pady=2,
        ).pack()

    def _hide(self, event=None):
        self._cancel()
        if self._tip is not None:
            try:
                self._tip.destroy()
            except Exception:
                pass
            self._tip = None


def _make_magnifier_icon(sign: str, size: int = 14, color: str = "#333333", bg: Optional[str] = "#f0f0f0"):
    """A tiny magnifying-glass icon (circle + handle, with a +/- drawn
    inside) built from raw pixel data -- avoids relying on an emoji glyph
    that isn't available in every system's default UI font."""
    img = tk.PhotoImage(width=size, height=size)
    if bg:  # None -> transparent, so the icon works on any (hover) button color
        img.put(bg, to=(0, 0, size, size))
    cx, cy, r = size // 2 - 2, size // 2 - 2, size // 2 - 4
    for y in range(size):
        for x in range(size):
            dist = ((x - cx) ** 2 + (y - cy) ** 2) ** 0.5
            if r - 1 <= dist <= r + 0.5:
                img.put(color, (x, y))
    for i in range(max(3, size // 4)):
        x, y = cx + r - 1 + i, cy + r - 1 + i
        if 0 <= x < size and 0 <= y < size:
            img.put(color, (x, y))
            if x + 1 < size:
                img.put(color, (x + 1, y))
    mid = cy
    half = max(1, r // 2)
    for x in range(cx - half, cx + half + 1):
        if 0 <= x < size:
            img.put(color, (x, mid))
    if sign == "+":
        for y in range(cy - half, cy + half + 1):
            if 0 <= y < size:
                img.put(color, (cx, y))
    return img


# ---------------------------------------------------------------------------
# Toolbar look: dark, to match the waveform canvas. Classic Tk widgets with
# explicit colors (ttk themes ignore/override colors differently per
# platform, and default text colors follow the desktop theme).
# ---------------------------------------------------------------------------
TB_BG = "#252526"
TB_BTN = "#333336"
TB_HOVER = "#45494e"
TB_PRESS = "#555a60"
TB_FG = "#e0e0e0"
TB_DIM = "#9a9a9a"
TB_DISABLED = "#6a6a6a"
TB_ACCENT = "#4fc3f7"
TB_LOOP = "#f0b429"
TB_WARN = "#f0b429"
TB_SEP = "#48484c"
TB_READOUT_BG = "#1b1b1c"
TB_FONT = ("TkDefaultFont", 10)
TB_MONO = ("TkFixedFont", 10)


def _tb_hover(widget, normal_bg=TB_BTN):
    def enter(_e):
        if str(widget.cget("state")) != "disabled":
            widget.configure(bg=TB_HOVER)
    widget.bind("<Enter>", enter, add="+")
    widget.bind("<Leave>", lambda _e: widget.configure(bg=normal_bg), add="+")


def _tb_button(parent, text="", command=None, width=None, image=None, fg=TB_FG):
    """A flat, dark toolbar button with hover highlight and hand cursor."""
    kw = dict(text=text, command=command, bg=TB_BTN, fg=fg, activebackground=TB_PRESS,
              activeforeground=fg, disabledforeground=TB_DISABLED, relief="flat", bd=0,
              highlightthickness=0, padx=7, pady=3, cursor="hand2", font=TB_FONT, takefocus=0)
    if image is not None:
        kw.update(image=image, compound="center" if not text else "left")
    if width is not None:
        kw["width"] = width
    btn = tk.Button(parent, **kw)
    _tb_hover(btn)
    return btn


def _tb_menubutton(parent, text):
    mb = tk.Menubutton(parent, text=text, bg=TB_BTN, fg=TB_FG, activebackground=TB_HOVER,
                       activeforeground=TB_FG, disabledforeground=TB_DISABLED, relief="flat", bd=0,
                       highlightthickness=0, padx=7, pady=3, cursor="hand2", font=TB_FONT, takefocus=0)
    _tb_hover(mb)
    menu = tk.Menu(mb, tearoff=False, bg="#2d2d30", fg=TB_FG, activebackground=TB_HOVER,
                   activeforeground="#ffffff", selectcolor=TB_ACCENT, bd=1,
                   disabledforeground=TB_DISABLED)      # Tk's default gray barely differs from TB_FG here
    mb.configure(menu=menu)
    return mb, menu


def _tb_separator(parent):
    tk.Frame(parent, width=1, height=20, bg=TB_SEP).pack(side="left", padx=8, pady=2)


# ---------------------------------------------------------------------------
# Missing playback-dependency UI (mirrors audio_tab.py's own pattern:
# detect what's missing, offer to pip install it, report back in the
# status area) -- but scoped to *playback only*, not the whole plugin, so
# marks/tracks editing still works even before/without installing it.
# ---------------------------------------------------------------------------

def _bind_undo_keys(tab, text):
    """Ctrl+Z / Ctrl+Y (and Ctrl+Shift+Z) in the text panel go to the tab's
    undo_hook/redo_hook when a plugin set them, else fall through to the
    Text widget's own undo. Bound once per tab; the handlers look the hooks
    up at key time, so they follow whatever file the tab holds now."""
    if text is None or getattr(tab, "_undo_keys_bound", False):
        return
    tab._undo_keys_bound = True

    def run(name):
        hook = getattr(tab, name, None)
        if hook:
            hook()
            return "break"
        return None

    for seq in ("<Control-z>", "<Control-Z>"):
        text.bind(seq, lambda e: run("undo_hook"), add="+")
    for seq in ("<Control-y>", "<Control-Y>", "<Control-Shift-z>", "<Control-Shift-Z>"):
        text.bind(seq, lambda e: run("redo_hook"), add="+")
    try:
        # The generated info text itself shouldn't be undoable.
        text.configure(undo=False)
    except tk.TclError:
        pass


def _decoder_hint(filepath):
    """One-line explanation of what's needed to decode this file, for the
    canvas error message and the text panel."""
    ext = Path(filepath).suffix.lower()
    if ext == ".mp4":
        return "MP4 audio needs ffmpeg/ffprobe on PATH."
    return "Needs ffmpeg/ffprobe on PATH, or: pip install soundfile (or miniaudio)."


def _num_fmt(val, fmt) -> str:
    if isinstance(val, (int, float)):
        return f"{val:{fmt}}"
    return "\u2014" if val is None else str(val)


def _metadata_text(filepath):
    """The old audio_tab.py's metadata block, as styled text. TinyTag when
    installed, else the Sequence Editor's built-in ID3/MP4 readers."""
    meta = th.read_metadata(filepath)
    dash = "\u2014"
    out = ""
    if meta.get("error") and len(meta) <= 2:
        debug(1, f"{{red}}metadata error: {meta['error']}")
        return f"{{red}}metadata error: {meta['error']}\n"
    dur = th.format_time_ms(meta["duration"]) if meta.get("duration") else dash
    out += (
        f"{{blue}}Title:  {{cyan}}{meta.get('title') or dash}\n"
        f"{{blue}}Artist: {{cyan}}{meta.get('artist') or dash}\n"
        f"{{blue}}Album:  {{cyan}}{meta.get('album') or dash}\n"
    )
    if meta["source"] == "tinytag":
        out += (
            f"{{blue}}Duration: {{cyan}}{dur}\n"
            f"{{blue}}Sample rate: {{cyan}}{_num_fmt(meta.get('samplerate'), '.0f')}\n"
            f"{{blue}}Channels: {{cyan}}{_num_fmt(meta.get('channels'), '.0f')}\n"
            f"{{blue}}Bitrate: {{cyan}}{_num_fmt(meta.get('bitrate'), '.1f')}\n"
        )
    else:
        for key, label in (("year", "Year"), ("genre", "Genre"), ("track_number", "Track #"),
                           ("composer", "Composer"), ("comment", "Comment")):
            if meta.get(key):
                out += f"{{blue}}{label}: {{cyan}}{meta[key]}\n"
        if meta.get("duration"):
            out += f"{{blue}}Duration: {{cyan}}{dur}\n"
        out += "{yellow}(built-in tag reader; pip install tinytag for sample rate/bitrate)\n"
    if meta.get("error"):
        out += f"{{yellow}}({meta['error']})\n"
    return out


_MARK_CLIPBOARD = {"marks": []}    # shared by all audio tabs (copy marks between songs too)

DLG_BG = "#f4f4f4"
DLG_FG = "#1e1e1e"
DLG_DIM = "#666666"
DLG_LOG_BG = "#1e1e1e"
DLG_LOG_FG = "#d4d4d4"


DLG_BUSY_BG = "#fff3b0"      # the row being installed
DLG_OK_FG = "#2e7d32"
DLG_BAD_FG = "#b00020"


class InstallDialog:
    """The \u26a0 Install button's window: every missing dependency (see
    deps.py) with what it's for and its download size, a check box each,
    and "All missing". Installs them one by one in a worker thread, the
    row being installed highlighted and pip's output in a log box; each
    row then shows \u2713 or \u2717. The result -- and a Restart button
    (new packages are only picked up by a fresh start) -- appear in this
    window rather than in a separate message box that could end up behind
    it. Classic Tk widgets with explicit colors."""

    def __init__(self, parent, on_done=None, restart=None):
        self.on_done = on_done
        self.restart = restart
        self.items = deps.missing(include_broken=False)
        self.vars = {}
        self.rows = {}
        self.busy = False
        top = self.top = tk.Toplevel(parent)
        top.title("Install optional packages")
        top.configure(bg=DLG_BG)
        try:
            top.transient(parent.winfo_toplevel())
        except tk.TclError:
            pass
        self.header = tk.Label(top, text="These packages are missing. Pick the ones you want; trackED works "
                                         "without them,\nbut the features listed next to each need them.",
                               bg=DLG_BG, fg=DLG_FG, justify="left", anchor="w")
        self.header.pack(fill="x", padx=12, pady=(10, 6))
        box = tk.Frame(top, bg=DLG_BG)
        box.pack(fill="x", padx=12)
        self.all_var = tk.BooleanVar(value=True)
        tk.Checkbutton(box, text="All missing", variable=self.all_var, command=self._toggle_all,
                       bg=DLG_BG, fg=DLG_FG, activebackground=DLG_BG, activeforeground=DLG_FG,
                       selectcolor="#ffffff", font=("TkDefaultFont", 10, "bold")).grid(row=0, column=0, sticky="w")
        for row, dep in enumerate(self.items, start=1):
            var = tk.BooleanVar(value=True)
            self.vars[dep["key"]] = var
            check = tk.Checkbutton(box, text=dep["key"], variable=var, command=self._sync_all,
                                   bg=DLG_BG, fg=DLG_FG, activebackground=DLG_BG, activeforeground=DLG_FG,
                                   selectcolor="#ffffff")
            check.grid(row=row, column=0, sticky="w", padx=(16, 8))
            purpose = tk.Label(box, text=dep["purpose"], bg=DLG_BG, fg=DLG_FG, anchor="w")
            purpose.grid(row=row, column=1, sticky="w")
            size = tk.Label(box, text=dep["size"], bg=DLG_BG, fg=DLG_DIM, anchor="w")
            size.grid(row=row, column=2, sticky="w", padx=(12, 0))
            state = tk.Label(box, text="", bg=DLG_BG, fg=DLG_FG, anchor="w", width=14)
            state.grid(row=row, column=3, sticky="w", padx=(8, 0))
            self.rows[dep["key"]] = (check, purpose, size, state)
        broken = [(d, deps.status(d)[1]) for d in deps.DEPENDENCIES if deps.status(d)[0] == "broken"]
        for dep, note in broken:
            tk.Label(top, text=f"{dep['key']}: {note}", bg=DLG_BG, fg=DLG_BAD_FG,
                     justify="left").pack(anchor="w", padx=12, pady=(6, 0))
        self.log = tk.Text(top, height=10, width=90, bg=DLG_LOG_BG, fg=DLG_LOG_FG, insertbackground=DLG_LOG_FG,
                           wrap="word", state="disabled")
        self.log.pack(fill="both", expand=True, padx=12, pady=(10, 4))
        btns = tk.Frame(top, bg=DLG_BG)
        btns.pack(fill="x", padx=12, pady=(4, 10))
        self.close_btn = tk.Button(btns, text="Close", command=self.close, bg="#e0e0e0", fg=DLG_FG,
                                   activebackground="#d0d0d0", activeforeground=DLG_FG)
        self.close_btn.pack(side="right")
        self.install_btn = tk.Button(btns, text="Install selected", command=self.install, bg="#2e7d32", fg="#ffffff",
                                     activebackground="#388e3c", activeforeground="#ffffff")
        self.install_btn.pack(side="right", padx=(0, 8))
        self.restart_btn = tk.Button(btns, text="\u27f3 Restart trackED now", command=self._restart,
                                     bg="#1565c0", fg="#ffffff", activebackground="#1976d2", activeforeground="#ffffff")
        top.protocol("WM_DELETE_WINDOW", self.close)

    def _toggle_all(self):
        for key, var in self.vars.items():
            if str(self.rows[key][0].cget("state")) != "disabled":
                var.set(bool(self.all_var.get()))

    def _sync_all(self):
        self.all_var.set(all(v.get() for v in self.vars.values()))

    def selected(self):
        return [k for k, v in self.vars.items() if v.get()]

    def _log(self, line):
        try:
            self.log.configure(state="normal")
            self.log.insert("end", line + "\n")
            self.log.see("end")
            self.log.configure(state="disabled")
        except tk.TclError:
            pass

    def _row_state(self, key, state):
        """Highlight the row being installed; then \u2713 / \u2717."""
        row = self.rows.get(key)
        if row is None:
            return
        check, purpose, size, label = row
        bg = DLG_BUSY_BG if state == "start" else DLG_BG
        text, fg = {"start": ("installing...", DLG_FG), "ok": ("\u2713 installed", DLG_OK_FG),
                    "failed": ("\u2717 failed", DLG_BAD_FG)}[state]
        try:
            for w in row:
                w.configure(bg=bg)
            check.configure(activebackground=bg)
            label.configure(text=text, fg=fg)
            if state == "ok":
                self.vars[key].set(False)
                check.configure(state="disabled")
        except tk.TclError:
            pass

    def install(self):
        keys = self.selected()
        if self.busy or not keys:
            return
        self.busy = True
        self.install_btn.configure(state="disabled", text="Installing...")
        self._log("Installing " + ", ".join(keys) + " -- large packages can take several minutes.")
        events = []
        lock = threading.Lock()

        def log(line):                     # worker thread: queue only, never touch Tk
            with lock:
                events.append(("log", line))

        def on_step(key, state):
            with lock:
                events.append(("step", key, state))

        def worker():
            result = deps.install(keys, log=log, on_step=on_step)
            with lock:
                events.append(("done", result))

        def pump():
            with lock:
                batch, events[:] = list(events), []
            for ev in batch:
                if ev[0] == "log":
                    self._log(ev[1])
                elif ev[0] == "step":
                    self._row_state(ev[1], ev[2])
                else:
                    self._finished(*ev[1])
                    return
            try:
                self.top.after(150, pump)
            except tk.TclError:
                pass

        threading.Thread(target=worker, daemon=True).start()
        self.top.after(150, pump)

    def _finished(self, ok, failed):
        self.busy = False
        for key, why in failed:
            self._log(f"NOT installed: {key} -- {why}")
        if ok:
            self._log("Installed: " + ", ".join(ok))
        still = [k for k in self.vars if k not in ok]
        self.install_btn.configure(state="normal" if still else "disabled", text="Install selected")
        if ok:
            msg = ("\u2713 Installed: " + ", ".join(ok) + ".\nRestart trackED to use "
                   + ("it." if len(ok) == 1 else "them.") + (f"  Not installed: {', '.join(k for k, _ in failed)}."
                                                            if failed else ""))
            self.header.configure(text=msg, fg=DLG_OK_FG, font=("TkDefaultFont", 10, "bold"))
            self.restart_btn.pack(side="left")
        elif failed:
            self.header.configure(text="Nothing was installed -- see the log below.", fg=DLG_BAD_FG)
        if self.on_done:
            self.on_done(ok, failed)

    def _restart(self):
        if self.restart:
            self.restart()

    def close(self):
        if self.busy and not messagebox.askyesno(
                "Install", "An install is still running. Close this window anyway?\n"
                           "(The install keeps running in the background.)", parent=self.top):
            return
        try:
            self.top.destroy()
        except tk.TclError:
            pass


class VoiceExportDialog:
    """Track menu > Export per Voice: which timing tracks to write (one per
    voice; optionally "All voices" only and every card), and whether the
    cards for all voices (no voice set) go into each voice's track. Then a
    Save dialog; the file type (xLights / LRC / Audacity) comes from the
    extension, as for Export Combined."""

    def __init__(self, parent, ctl, track, marks):
        self.ctl, self.track, self.marks = ctl, track, marks
        voices = th.voices_in(marks, getattr(ctl, "voices", []))
        top = self.top = tk.Toplevel(parent)
        top.title(f"Export per Voice \u2013 {track['name']}")
        top.configure(bg=DLG_BG)
        tk.Label(top, text="Timing tracks to write:", bg=DLG_BG, fg=DLG_FG,
                 font=("TkDefaultFont", 10, "bold")).pack(anchor="w", padx=12, pady=(10, 4))
        self.vars = []
        n_all = sum(1 for m in marks if not th.effective_voices(m))
        choices = [(v, f"{track['name']} - {v}", True) for v in voices]
        choices.append((th.ALL_VOICES_NAME, f"{track['name']} - All voices  (only the {n_all} cards for all voices)",
                        not voices))
        choices.append((th.ANY_VOICE, f"{track['name']}  (every card, any voice)", False))
        for key, text, on in choices:
            var = tk.BooleanVar(value=on)
            self.vars.append((key, var))
            tk.Checkbutton(top, text=text, variable=var, bg=DLG_BG, fg=DLG_FG, activebackground=DLG_BG,
                           activeforeground=DLG_FG, selectcolor="#ffffff").pack(anchor="w", padx=24)
        self.each_var = tk.BooleanVar(value=True)
        tk.Checkbutton(top, text="Cards for \u201cAll voices\u201d (no voice set) also go into each voice's track",
                       variable=self.each_var, bg=DLG_BG, fg=DLG_FG, activebackground=DLG_BG,
                       activeforeground=DLG_FG, selectcolor="#ffffff").pack(anchor="w", padx=12, pady=(8, 0))
        if not voices:
            tk.Label(top, text="No card has a voice yet: use a card's Voice \u25be button to assign one.",
                     bg=DLG_BG, fg=DLG_DIM).pack(anchor="w", padx=12, pady=(6, 0))
        btns = tk.Frame(top, bg=DLG_BG)
        btns.pack(fill="x", padx=12, pady=10)
        tk.Button(btns, text="Cancel", command=top.destroy, bg="#e0e0e0", fg=DLG_FG,
                  activebackground="#d0d0d0", activeforeground=DLG_FG).pack(side="right")
        tk.Button(btns, text="Export...", command=self.export, bg="#2e7d32", fg="#ffffff",
                  activebackground="#388e3c", activeforeground="#ffffff").pack(side="right", padx=(0, 8))

    def tracks(self):
        outputs = [key for key, var in self.vars if var.get()]
        return th.voice_export_tracks(self.track["name"], self.marks, outputs, bool(self.each_var.get()))

    def export(self, path=None):
        tracks = self.tracks()
        if not tracks:
            messagebox.showinfo("Export per Voice", "Nothing to export: no checked track has any cards.",
                                parent=self.top)
            return False
        if path is None:
            path = self.ctl.ask_export_path("Export per Voice", f"{self.track['name']}-voices.xtiming",
                                            parent=self.top)
        if not path:
            return False
        overlaps = [(name, th.overlap_count(ms)) for name, ms in tracks]
        overlaps = [(n, c) for n, c in overlaps if c]
        try:
            th.export_timing_tracks(path, tracks)
        except Exception as exc:
            messagebox.showerror("Export per Voice", f"Could not export:\n{exc}", parent=self.top)
            return False
        debug(1, f"{{green}}Exported {len(tracks)} voice track(s) of '{self.track['name']}' to {path}")
        if hasattr(self.ctl, "_exported"):
            self.ctl._exported(len(tracks), path)
        if overlaps:
            messagebox.showwarning("Export per Voice",
                                   "Exported, but these tracks have overlapping cards, which xLights shows "
                                   "oddly:\n\n" + "\n".join(f"  {n}: {c} overlap(s)" for n, c in overlaps),
                                   parent=self.top)
        try:
            self.top.destroy()
        except tk.TclError:
            pass
        return True


def _explained(error, what):
    """aa.explain_error for the text panel: the error in red, the advice
    (its following lines) in yellow."""
    text = aa.explain_error(error, what) if isinstance(error, BaseException) else str(error)
    return text.replace("\n", "\n{yellow}")


def _restart_app(widget):
    """Ask trackED (tracked.EditorApp.restart) to save and start again."""
    try:
        app = widget.winfo_toplevel()
    except tk.TclError:
        return False
    restart = getattr(app, "restart", None)
    if callable(restart):
        restart()
        return True
    return False


# ---------------------------------------------------------------------------
# WaveformController -- the plugin's main object. One per claimed canvas.
# ---------------------------------------------------------------------------

class WaveformController:
    """Owns the canvas' toolbar rows and drawing/interaction for one
    media file: waveform, timing marks/tracks, and playback. Analogous
    to audio_tab.py's own WaveformPlayer, but adding the marks/tracks
    layer that project doesn't have."""

    LABEL_ZONE_HEIGHT = 24
    TRACK_HEIGHT = 30
    STATUS_ROW_HEIGHT = 22  # combined status / new-track drop row under the waveform
    OVERSHOOT_FACTOR = 1.1  # zooming out past "fit" shows this much of the duration (10% past the end)
    DRAG_SNAP_STEPS = 200   # dragging a mark snaps to a "nice" step of about 1/200 of the view (Shift: no snap)
    SEEK_CLICK_WINDOW = 0.6  # s: a skip click this soon after a double/triple-click seek repeats the seek
    TRACK_PALETTE = ["#3a86ff", "#ff6b6b", "#51cf66", "#ffb703"]
    SELECTION_COLOR = "#ffe066"
    EDGE_ZONE = 10
    UNDO_LIMIT = 20  # marks/tracks undo steps kept (no per-app preference here, unlike the original)

    def __init__(self, canvas: tk.Canvas, text: Optional[tk.Text], filepath: str, tab=None):
        self.canvas = canvas
        self.text = text
        self.filepath = filepath
        self.tab = tab
        self.parent = canvas.master  # top_frame, per editor_tab.py's layout

        # -- waveform/view state --
        self.audio_duration: Optional[float] = None
        self.full_peaks = []
        self.peaks = []
        self.view_start = 0.0
        self.view_end = 0.0
        self._view_gen = 0              # bumps on every view change (drops stale detail decodes)
        self._detail_after_id = None    # pending debounced detail decode

        # -- marks/tracks state --
        self.marks = th.load_marks(filepath)
        self.tracks = th.load_tracks(filepath)
        # Voice names for this file; marks list theirs in mark["voices"].
        self.voices = th.merge_voice_lists(th.load_voices(filepath),
                                           *[m.get("voices") for m in self.marks])
        self.selected = None   # ("mark", id) | ("track", id) | None
        self._hover = None
        self._mark_hit_regions = {}
        self._track_label_regions = {}
        self._track_band_regions = {}
        self._move_drag = None
        self._track_drag = None
        self._press_info = None
        self._preview_range = None
        self._mark_history = [self._mark_snapshot()]
        self._mark_history_index = 0
        self._history_views = [None]      # the zoom/scroll each step was made in (undo/redo returns there)

        # -- stem regions / analysis state --
        self.region_colors = stem_colors()
        self._raw_regions = th.load_regions(filepath)      # as analyzed (saved in the cache)
        self.regions = aa.smooth_regions(self._raw_regions, get_stem_min_seconds())
        self._region_starts = [r["start"] for r in self.regions]
        self._analysis_busy = None   # None | "stems" | "transcribe"
        self.info_text = ""          # the tab's normal text-panel content (see set_info_text)
        self.panel = TimingPanel(self, text) if text is not None else None

        # -- time cursor (Ctrl+click), used by Split / "@" when not playing --
        self.cursor_time = 0.0

        # -- playback state --
        self.engine = th.make_playback_engine()
        self._play_state = "stopped"  # "stopped" | "playing" | "paused"
        self._play_seg_start = 0.0
        self._play_seg_end: Optional[float] = None
        self._play_position = 0.0
        self._play_origin = 0.0       # the @cursor when Play was pressed (paused + Play returns here)
        self._last_click_mark_id = None  # point made by the last plain click (Shift+click extends it)
        self._play_speed = 1.0
        self._play_started_wall: Optional[float] = None
        self._loop = False            # Shift+Play: repeat the segment until stopped
        self._play_mark_id = None     # the mark whose span is playing (for the card Play/Pause buttons)
        self._shift_on_play = False

        self._build_toolbars()
        self._setup_file_drop()
        self._configure_canvas()
        self._start_load()

    # ------------------------------------------------------------------ setup
    def _build_toolbars(self):
        """One grouped toolbar row above the waveform -- transport | view |
        analysis -- and a status strip below it (playback state, visible
        range, analysis progress, region color key)."""
        # Clear any toolbar rows a previous onload() call on this same
        # canvas/tab left behind (editor_tab.py clears the canvas' own
        # children on reload, but not sibling frames packed into
        # canvas.master alongside it).
        for w in getattr(self.canvas, "_waveform_toolbars", []):
            try:
                w.destroy()
            except Exception:
                pass
        toolbars = []

        bar = tk.Frame(self.parent, bg=TB_BG, padx=4, pady=3)
        bar.pack(side="top", fill="x", before=self.canvas)
        toolbars.append(bar)

        # -- transport --
        self.play_back_btn = _tb_button(bar, "\u25c0\u25c0", lambda: self.skip_play(-5.0))
        self.play_btn = _tb_button(bar, "\u25b6", self.toggle_play, width=2)
        self.play_fwd_btn = _tb_button(bar, "\u25b6\u25b6", lambda: self.skip_play(5.0))
        for btn in (self.play_back_btn, self.play_btn, self.play_fwd_btn):
            btn.pack(side="left", padx=(0, 2))
        _Tooltip(self.play_back_btn, "Back 5 seconds\nShift+click: start of the stem region\n"
                                     "Ctrl+click: start of the audio")
        # Remember the modifier keys on release (widget bindings run before
        # the class binding that invokes the command).
        for btn in (self.play_back_btn, self.play_fwd_btn):
            btn.bind("<ButtonRelease-1>", lambda e: setattr(self, "_skip_mods", e.state), add="+")
            register_modifier_button(btn, ("control", "shift"))     # skip_play checks Ctrl first
        _Tooltip(self.play_btn, "Play from the @cursor / pause\n"
                                "While paused: Play starts again from where it started (or from the\n"
                                "@cursor if you moved it); Ctrl+click resumes from the paused spot\n"
                                "Shift+click: loop (from the @cursor to the end of the selected range,\n"
                                "or the selected mark from its start) until paused")
        _Tooltip(self.play_fwd_btn, "Forward 5 seconds\nShift+click: end of the stem region\n"
                                    "Ctrl+click: end of the audio")
        # Shift detection for the Play button: remember Shift on release
        # (widget bindings run before the class binding that invokes the
        # command), and show a loop cursor while Shift is held over it.
        self.play_btn.bind("<ButtonRelease-1>", self._on_play_btn_release, add="+")
        register_modifier_button(self.play_btn, ("shift", "control"))
        self.play_btn.bind("<Enter>", lambda e: self._set_play_cursor(bool(e.state & SHIFT_MASK)), add="+")
        self.play_btn.bind("<Motion>", lambda e: self._set_play_cursor(bool(e.state & SHIFT_MASK)), add="+")
        self.play_btn.bind("<Leave>", lambda e: self._set_play_cursor(False), add="+")
        self._bind_shift_keys()

        self.play_speed_var = tk.StringVar(value="1x")
        self.speed_btn, speed_menu = _tb_menubutton(bar, "1x \u25be")
        for choice in ("0.5x", "1x", "2x"):
            speed_menu.add_radiobutton(label=choice, value=choice, variable=self.play_speed_var,
                                       command=self._on_play_speed_changed)
        self.speed_btn.pack(side="left", padx=(4, 0))
        _Tooltip(self.speed_btn, "Playback speed")

        # Volume (persisted): - / level / +
        self.volume = self._saved_volume()
        self.engine.set_volume(self.volume)
        self.vol_down_btn = _tb_button(bar, "\u2212", lambda: self.change_volume(-self.VOLUME_STEP))
        self.vol_label = tk.Label(bar, text="", width=8, bg=TB_BG, fg=TB_DIM, font=TB_FONT)
        self.vol_up_btn = _tb_button(bar, "+", lambda: self.change_volume(self.VOLUME_STEP))
        self.vol_down_btn.pack(side="left", padx=(6, 0))
        self.vol_label.pack(side="left")
        self.vol_up_btn.pack(side="left")
        _Tooltip(self.vol_down_btn, "Volume down")
        _Tooltip(self.vol_up_btn, "Volume up")
        self._update_volume_label()

        # Fixed-width, monospaced position readout (current / total), so the
        # controls to its right never shift as the numbers change.
        # The position is an entry: type a time + Enter to move the @cursor.
        self.time_var = tk.StringVar(value="--:--.--- / --:--.---")
        readout = tk.Frame(bar, bg=TB_READOUT_BG, padx=4, pady=1)
        readout.pack(side="left", padx=(8, 0))
        self.pos_entry = tk.Entry(readout, width=10, justify="right", font=TB_MONO, bg=TB_READOUT_BG, fg=TB_FG,
                                  insertbackground=TB_FG, relief="flat", bd=0, highlightthickness=1,
                                  highlightbackground=TB_READOUT_BG, highlightcolor=TB_ACCENT,
                                  selectbackground="#264f78", selectforeground="#ffffff")
        self.pos_entry.pack(side="left")
        self.total_label = tk.Label(readout, text="/ --:--.---", bg=TB_READOUT_BG, fg=TB_DIM, font=TB_MONO)
        self.total_label.pack(side="left", padx=(4, 2))
        self.pos_entry.bind("<Return>", self._on_pos_entered)
        self.pos_entry.bind("<KP_Enter>", self._on_pos_entered)
        self.pos_entry.bind("<Escape>", lambda e: (self._update_time_readout(force=True), self.canvas.focus_set(), "break")[2])
        self.pos_entry.bind("<FocusIn>", lambda e: self.pos_entry.after(1, lambda: self.pos_entry.select_range(0, "end")))
        _Tooltip(self.pos_entry, "@cursor (= playhead). Type a time (m:ss.mmm or seconds) + Enter to move it.\n"
                                 "Click the waveform to move it; M adds a point mark at it.")

        _tb_separator(bar)

        # -- view --
        self._zoom_out_icon = _make_magnifier_icon("-", color=TB_FG, bg=None)
        self._zoom_in_icon = _make_magnifier_icon("+", color=TB_FG, bg=None)
        self.jump_start_btn = _tb_button(bar, "|\u25c0", lambda: self.jump_waveform_edge("start"))
        self.zoom_out_btn = _tb_button(bar, image=self._zoom_out_icon, command=lambda: self.zoom_waveform("out"))
        self.zoom_fit_btn = _tb_button(bar, "\u2194", lambda: self.zoom_waveform("fit"))
        self.zoom_in_btn = _tb_button(bar, image=self._zoom_in_icon, command=lambda: self.zoom_waveform("in"))
        self.jump_end_btn = _tb_button(bar, "\u25b6|", lambda: self.jump_waveform_edge("end"))
        for btn in (self.jump_start_btn, self.zoom_out_btn, self.zoom_fit_btn, self.zoom_in_btn, self.jump_end_btn):
            btn.pack(side="left", padx=(0, 2), fill="y")
        _Tooltip(self.jump_start_btn, "Jump to start")
        _Tooltip(self.zoom_out_btn, "Zoom out (or mouse wheel)")
        _Tooltip(self.zoom_fit_btn, "Fit whole waveform in view")
        _Tooltip(self.zoom_in_btn, "Zoom in (or mouse wheel)")
        _Tooltip(self.jump_end_btn, "Jump to end")

        # -- navigator: visible range + a slider (its thumb = the visible
        # part of the audio; drag it, or click beside it, to scroll) --
        self.view_var = tk.StringVar(value="")
        tk.Label(bar, textvariable=self.view_var, bg=TB_BG, fg=TB_DIM, font=("TkFixedFont", 9)).pack(
            side="left", padx=(10, 6))
        self.nav = tk.Canvas(bar, width=self.NAV_WIDTH, height=12, bg=TB_BG, highlightthickness=0, cursor="hand2")
        self.nav.pack(side="left")
        self.nav.bind("<ButtonPress-1>", self._on_nav_press)
        self.nav.bind("<B1-Motion>", self._on_nav_drag)
        self.nav.bind("<Configure>", lambda e: self._draw_nav())
        _Tooltip(self.nav, "Visible part of the audio: drag to scroll, click to jump there")

        # -- analysis (right) --
        right = tk.Frame(bar, bg=TB_BG)
        right.pack(side="right")
        self.stems_btn = _tb_button(right, "Stems", self.run_stem_analysis)
        self.stems_btn.pack(side="left", padx=(0, 4))
        _Tooltip(self.stems_btn, "Separate vocals / instrumental with demucs (cached next to the audio\n"
                                 "file) and color the waveform: green = vocal, blue = instrumental, "
                                 "teal = mixed.\nClick the color key under the waveform to change colors.\n"
                                 "Shift+click to re-run even if cached.")
        self.stems_btn.bind("<ButtonRelease-1>",
                            lambda e: setattr(self, "_force_stems", bool(e.state & SHIFT_MASK)), add="+")
        register_modifier_button(self.stems_btn, ("shift",))
        # Stems \u25be: turn the (non-empty) stem regions into timing tracks.
        self.stems_menu_btn, self.stems_menu = _tb_menubutton(right, "\u25be")
        self.stems_menu_btn.configure(padx=4)
        self.stems_menu_btn.pack(side="left", padx=(0, 6), before=self.stems_btn)
        self.stems_btn.pack_configure(padx=(0, 1))
        self.stems_btn.pack(side="left", before=self.stems_menu_btn)
        self.stems_menu.configure(postcommand=self._fill_stems_menu)
        _Tooltip(self.stems_menu_btn, "Create timing tracks from the stem regions")
        self.mood_btn = _tb_button(right, "Mood", self.run_genre_mood)
        self.mood_btn.pack(side="left", padx=(0, 6))
        self.mood_btn.bind("<ButtonRelease-1>",
                           lambda e: setattr(self, "_force_mood", bool(e.state & SHIFT_MASK)), add="+")
        register_modifier_button(self.mood_btn, ("shift",))
        _Tooltip(self.mood_btn, "Estimate the overall genre and mood (rule-based guess from tempo,\n"
                                "loudness and spectrum; lyrics from Transcribe help). Needs librosa.\n"
                                "The result is cached with the file until the audio file changes;\n"
                                "Shift+click to re-run anyway (e.g. after adding lyrics).")
        # Beats \u25be: bars / beats / metronome timing tracks.
        self.beats_btn, self.beats_menu = _tb_menubutton(right, "Beats \u25be")
        self.beats_btn.pack(side="left", padx=(0, 6))
        self.beats_menu.configure(postcommand=self._fill_beats_menu)
        _Tooltip(self.beats_btn, "Bars / beats as a new timing track (beat detection needs librosa).\n"
                                 "Where (in the menu): the selected range, else the whole song;\n"
                                 "or from the @cursor to the end; or always the whole song.")
        # Structure \u25be: intro / verse / chorus ... sections as a timing track.
        self.structure_btn, self.structure_menu = _tb_menubutton(right, "Structure \u25be")
        self.structure_btn.pack(side="left", padx=(0, 6))
        self.structure_menu.configure(postcommand=self._fill_structure_menu)
        _Tooltip(self.structure_btn, "Find the song's sections (intro, verse, chorus, bridge, ...) from how\n"
                                     "the music repeats, as a new \u201cStructure\u201d timing track.\n"
                                     "Names are a rule-based guess; repeated parts share a letter (A, B, ...).\n"
                                     "Needs librosa. Run Stems first to help tell instrumental parts.")
        self.transcribe_btn = _tb_button(right, "Transcribe", self.transcribe_selected)
        self.transcribe_btn.pack(side="left", padx=(0, 1))
        _Tooltip(self.transcribe_btn, "Transcribe with Whisper:\n"
                                      "  a range selected \u2014 its vocals become the range's text (label)\n"
                                      "  nothing selected \u2014 the whole song goes into a new \u201cTranscript\u201d\n"
                                      "  timing track, one card per sung phrase")
        self.model_var = tk.StringVar()
        self._merge_var = tk.BooleanVar(value=bool(get_preference("stem_track_merge", True)))
        self.model_btn, self.model_menu = _tb_menubutton(right, "\u25be")
        self.model_btn.configure(padx=4)
        self.model_btn.pack(side="left")
        self._refresh_model_combo()
        # Warning slot: the install button only appears when packages are missing.
        self._warn_slot = tk.Frame(right, bg=TB_BG)
        self._warn_slot.pack(side="left")
        self.install_btn = _tb_button(self._warn_slot, "\u26a0", self._on_install_clicked, fg=TB_WARN)
        self._install_tip = _Tooltip(self.install_btn, "")

        # Status texts are drawn on the canvas in the row under the waveform
        # (see _render_status_row); a change redraws it (coalesced).
        self.play_status_var = tk.StringVar(value="")
        self.analysis_status_var = tk.StringVar(value="")
        for var in (self.play_status_var, self.analysis_status_var):
            try:
                var.trace_add("write", lambda *_a: self._schedule_status_redraw())
            except (AttributeError, tk.TclError):
                pass
        self._refresh_playback_availability()
        self._update_play_controls()   # Stop starts hidden (only shown while paused)

        self.canvas._waveform_toolbars = toolbars
        self._toolbars = toolbars

    # ------------------------------------------------------------------ panel sizing
    # editor_tab.py restores each tab's sash from session data, defaulting
    # to utils.DEFAULT_SASH_POS (60px) -- enough for a bare canvas, but this
    # plugin packs two toolbar rows above its canvas in that same pane, so
    # at 60px the canvas is squeezed to ~0px and the waveform never shows.
    # These two are handed to the tab as tab.min_sash / tab.preferred_sash
    # (see onload()) and are evaluated when editor_tab restores the sash,
    # i.e. after the toolbars have real requested heights.
    MIN_WORK_HEIGHT = 60       # smallest useful waveform area
    PREFERRED_WORK_HEIGHT = 130

    def _toolbar_height(self):
        total = 0
        for bar in getattr(self, "_toolbars", []):
            try:
                total += max(bar.winfo_reqheight(), 1)
            except tk.TclError:
                pass
        return total

    def min_panel_height(self):
        tracks_h = self.STATUS_ROW_HEIGHT + len(self.tracks) * self.TRACK_HEIGHT
        return self._toolbar_height() + self.MIN_WORK_HEIGHT + tracks_h

    def preferred_panel_height(self):
        tracks_h = self.STATUS_ROW_HEIGHT + len(self.tracks) * self.TRACK_HEIGHT
        return self._toolbar_height() + self.PREFERRED_WORK_HEIGHT + tracks_h

    def _canvas_size(self):
        """Actual canvas size, or its configured size while it isn't mapped
        yet (winfo_width/height report 1, not 0, for an unmapped widget, so
        a plain `or default` fallback never kicks in)."""
        c = self.canvas
        w, h = c.winfo_width(), c.winfo_height()
        if w <= 1:
            w = 600
        if h <= 1:
            try:
                h = int(float(c.cget("height")))
            except Exception:
                h = 160
        return w, h

    def _refresh_playback_availability(self):
        """Show the \u26a0 Install button while anything in deps.py is
        missing (or "Restart" once packages were installed). Doesn't block
        the waveform/marks/tracks UI."""
        playback_missing = bool(th.PLAYBACK_MISSING) and isinstance(self.engine, th.SoundDevicePlaybackEngine)
        if getattr(self, "_restart_pending", False):
            self.install_btn.configure(text="\u27f3 Restart", state="normal")
            self.install_btn.pack(side="left", padx=(6, 0))
            self._install_tip.text = "New packages were installed: restart trackED to use them"
            return
        missing = deps.missing()
        if missing or playback_missing:
            self.install_btn.configure(text="\u26a0 Install", state="normal")
            self.install_btn.pack(side="left", padx=(6, 0))
            self._install_tip.text = ("Missing: " + ", ".join(d["key"] for d in missing)
                                      + "\nClick to choose which to install")
            if playback_missing:
                self.play_status_var.set("Playback packages missing")
        else:
            self.install_btn.pack_forget()

    def _update_legend(self):
        """The region color key is drawn in the status row by render."""
        if self.audio_duration is not None:
            self._last_status_drawn = None   # the key changed even if the text didn't
            self._schedule_status_redraw()

    def _status_text(self):
        return " \u00b7 ".join(v for v in (self.play_status_var.get(), self.analysis_status_var.get()) if v)

    def _schedule_status_redraw(self):
        # Playback re-sets the same status 10x/s; only redraw on a real change.
        if self._status_text() == getattr(self, "_last_status_drawn", None):
            return
        if getattr(self, "_status_redraw_id", None) is None:
            try:
                self._status_redraw_id = self.canvas.after(30, self._status_redraw)
            except tk.TclError:
                pass

    def _status_redraw(self):
        self._status_redraw_id = None
        self.render_waveform()

    def _on_install_clicked(self):
        if getattr(self, "_restart_pending", False):
            _restart_app(self.canvas)
            return
        if getattr(self, "_install_dialog", None) is not None:
            try:
                if self._install_dialog.top.winfo_exists():
                    self._install_dialog.top.lift()
                    return
            except tk.TclError:
                pass
        self._install_dialog = InstallDialog(self.canvas, on_done=self._install_finished,
                                             restart=lambda: _restart_app(self.canvas))

    def _install_finished(self, ok, failed):
        """The dialog shows the result and its own Restart button; here the
        toolbar button turns into \u27f3 Restart."""
        aa.clear_probe_cache()
        if not ok:
            self.play_status_var.set("Install failed")
            return
        self._restart_pending = True
        self._refresh_playback_availability()
        self.play_status_var.set("Installed -- restart to use the new packages")

    def _configure_canvas(self):
        c = self.canvas
        c.configure(background="#1e1e1e", height=160)
        c.create_text(10, 80, text="Preparing waveform...", fill="#aaaaaa", anchor="w", tags="placeholder")
        c.bind("<Button-1>", self._on_waveform_press)
        # Ctrl+click / Ctrl+drag: place the time cursor (seek) without
        # creating a mark. More specific than <Button-1>, so Tk picks it.
        c.bind("<Control-Button-1>", self._on_ctrl_press)
        register_modifier_listener(self._show_modifier_hint, c)
        c.bind("<Control-B1-Motion>", self._on_ctrl_drag)
        c.bind("<Control-ButtonRelease-1>", lambda e: "break")
        c.bind("<B1-Motion>", self._on_waveform_drag)
        c.bind("<ButtonRelease-1>", self._on_waveform_release)
        c.bind("<Double-Button-1>", self._on_waveform_double_click)
        c.bind("<Motion>", self._on_waveform_motion)
        c.bind("<Button-3>", self._on_waveform_right_click)
        c.bind("<MouseWheel>", self._on_waveform_wheel)
        c.bind("<Button-4>", self._on_waveform_wheel)
        c.bind("<Button-5>", self._on_waveform_wheel)
        c.bind("<Configure>", self._on_canvas_configure)
        c.bind("<Enter>", lambda e: c.focus_set())
        c.bind("<Leave>", self._on_waveform_leave)
        c.bind("<Up>", self._on_key_up)
        c.bind("<Down>", self._on_key_down)
        c.bind("<Left>", self._on_key_left)
        c.bind("<Right>", self._on_key_right)
        c.bind("<Delete>", self._on_key_delete)
        c.bind("<Home>", lambda e: (self.select_end_mark(last=False), "break")[1])
        c.bind("<End>", lambda e: (self.select_end_mark(last=True), "break")[1])
        for key in ("<Key-m>", "<Key-M>"):
            c.bind(key, lambda e: (self.add_point_at(self.cursor_position() or 0.0), "break")[1])
        c.bind("<BackSpace>", self._on_key_delete)
        c.bind("<Escape>", self._on_key_escape)
        c.bind("<Tab>", self._on_key_tab)
        c.bind("<Shift-Tab>", self._on_key_shift_tab)
        c.bind("<ISO_Left_Tab>", self._on_key_shift_tab)
        # Bound directly on the canvas (not via bind_all on the app), same
        # fix as trackED.py's own undo()/redo() -- see the module docstring
        # of the Ctrl-Z/Ctrl-Y fix in trackED.py itself. A Text widget's
        # native undo binding and an app-wide bind_all would double-fire;
        # the canvas has no native undo binding to conflict with, so this
        # is the one safe place for marks/tracks undo/redo shortcuts.
        for key, fn in (("c", self.copy_selection), ("x", self.cut_selection), ("v", self.paste_marks)):
            c.bind(f"<Control-{key}>", lambda e, f_=fn: (f_(), "break")[1])
            c.bind(f"<Control-{key.upper()}>", lambda e, f_=fn: (f_(), "break")[1])
        c.bind("<Control-z>", lambda e: self.undo_marks())
        c.bind("<Control-y>", lambda e: self.redo_marks())

    def _set_zoom_controls_enabled(self, enabled: bool):
        state = "normal" if enabled else "disabled"
        for btn in (self.jump_start_btn, self.zoom_in_btn, self.zoom_out_btn,
                    self.zoom_fit_btn, self.jump_end_btn, self.speed_btn,
                    self.play_btn, self.play_back_btn, self.play_fwd_btn):
            btn.configure(state=state)

    # ------------------------------------------------------------------ loading
    def _start_load(self):
        """Threaded initial decode: duration + a cached (or freshly
        decoded) full-file waveform overview, mirroring the Sequence
        Editor's original open_media_file/finish_initial_waveform split.
        Also loads the file into the active playback engine."""
        result = {}

        def worker():
            try:
                cached = th.load_waveform_cache(self.filepath)
                if cached and len(cached["peaks"]) >= th.WAVEFORM_CACHE_RESOLUTION:
                    result["duration"] = cached["duration"]
                    result["peaks"] = cached["peaks"]
                else:
                    # No cache, or an older lower-resolution one: (re)decode.
                    duration = cached["duration"] if cached else th.get_audio_duration_seconds(self.filepath)
                    if duration is None:
                        result["error"] = "Could not determine audio duration.\n" + _decoder_hint(self.filepath)
                        result["details"] = list(th.LAST_DURATION_ERRORS)
                        return
                    peaks = th.decode_waveform_peaks(self.filepath, 0.0, duration, th.WAVEFORM_CACHE_RESOLUTION)
                    if not peaks:
                        result["error"] = "Could not decode waveform data.\n" + _decoder_hint(self.filepath)
                        return
                    th.save_waveform_cache(self.filepath, duration, peaks)
                    result["duration"] = duration
                    result["peaks"] = peaks
                self.engine.load(self.filepath)
            except Exception as exc:
                result["error"] = str(exc)

        thread = threading.Thread(target=worker, daemon=True)
        thread.start()

        def poll():
            if thread.is_alive():
                self.canvas.after(80, poll)
                return
            if "error" in result:
                self._show_waveform_error(result["error"])
                debug(1, f"{{red}}waveform_tab load error: {result['error']}")
                for line in result.get("details", []):
                    debug(1, f"{{red}}  {line}")
                return
            self._finish_initial_waveform(result["duration"], result["peaks"])

        self.canvas.after(80, poll)

    def _finish_initial_waveform(self, duration, peaks):
        self.audio_duration = duration
        self.view_start, self.view_end = 0.0, duration
        self.full_peaks = peaks
        self.peaks = th.rebucket_peaks(peaks, 0.0, 1.0, self._target_buckets())
        self._duration_text_base = th.format_time_ms(duration)
        if self.tab is not None:
            self.tab.title_detail = th.format_time_ms(duration)  # window title: "song.mp3 (3:45.120)"
            refresh = getattr(self.tab, "refresh_title", None)
            if callable(refresh):
                refresh()
        view_restored = self.restore_view()      # zoom / scroll from last time
        self.render_waveform()
        self._set_zoom_controls_enabled(True)
        self.restore_selection(reveal=not view_restored)   # the track / card selected last time
        self._remembered_state = self._view_state()        # nothing new to save yet
        debug(2, f"{{green}}waveform_tab loaded {self.filepath}: {th.format_time_ms(duration)}")
        self._auto_stems()

    def _show_waveform_error(self, message):
        self._duration_text_base = "unavailable"
        self.time_var.set("--:--.--- / unavailable")
        self.canvas.delete("all")
        w, h = self._canvas_size()
        self.canvas.create_text(w // 2, h // 2, text=message, fill="#e08080", width=w - 20, justify="center")

    # ------------------------------------------------------------------ zoom / pan
    def zoom_waveform(self, action):
        if self.audio_duration is None:
            return
        duration = self.audio_duration
        span = self.view_end - self.view_start
        mid = (self.view_start + self.view_end) / 2
        if action == "fit":
            new_start, new_end = 0.0, duration
        elif action == "in":
            new_span = max(0.05, span / 2)
            new_start = max(0.0, mid - new_span / 2)
            new_end = min(duration, new_start + new_span)
            new_start = max(0.0, new_end - new_span)
        elif action == "out":
            if span >= duration - 1e-9:
                # Already showing everything: one extra step leaves a little
                # room past the end, so marks near the end are easy to reach.
                new_start, new_end = 0.0, duration * self.OVERSHOOT_FACTOR
            else:
                new_span = min(duration, span * 2)
                new_start = max(0.0, mid - new_span / 2)
                new_end = min(duration, new_start + new_span)
                new_start = max(0.0, new_end - new_span)
        else:
            return
        self.view_start, self.view_end = new_start, new_end
        self._refresh_view_from_cache()

    def jump_waveform_edge(self, edge):
        if self.audio_duration is None:
            return
        duration = self.audio_duration
        span = self.view_end - self.view_start
        if edge == "start":
            self.view_start, self.view_end = 0.0, min(duration, span)
        elif edge == "end":
            self.view_end = duration
            self.view_start = max(0.0, duration - span)
        else:
            return
        self._refresh_view_from_cache()

    def _target_buckets(self):
        """One waveform column per canvas pixel (as in the Sequence
        Editor's _waveform_target_buckets)."""
        return max(50, min(3000, int(self._canvas_size()[0])))

    def _on_canvas_configure(self, event=None):
        if self.audio_duration:
            self._refresh_view_from_cache()
        else:
            self.render_waveform()

    DETAIL_BEHIND = 0.25     # pages of detail decoded before the view
    DETAIL_AHEAD = 1.75      # ...and after it (so the next page is already there)
    DETAIL_MAX_BUCKETS = 24000

    def _refresh_view_from_cache(self, render=True):
        """Set self.peaks for the current view.

        - The full-file overview has enough points for this view: rebucket it.
        - Zoomed in further: use the decoded detail cache if it covers the
          view at this zoom; otherwise show the coarse overview now and
          decode detail in the background for the view plus ~1.75 pages
          ahead (and a little behind), so scrolling on -- e.g. following
          the playhead -- needs no new decode. When the view comes within
          half a page of the detail's end, the next stretch is prefetched."""
        if not self.audio_duration:
            return
        duration = self.audio_duration
        data_end = min(self.view_end, duration)
        span = self.view_end - self.view_start
        share = (data_end - self.view_start) / span if span > 0 else 1.0
        self._peaks_span = (self.view_start, data_end)
        target = max(2, int(self._target_buckets() * share))
        start_frac, end_frac = self.view_start / duration, data_end / duration
        available = (end_frac - start_frac) * len(self.full_peaks or [])
        self._view_gen = getattr(self, "_view_gen", 0) + 1
        pending = getattr(self, "_detail_after_id", None)
        if pending is not None:
            try:
                self.canvas.after_cancel(pending)
            except (tk.TclError, ValueError):
                pass
            self._detail_after_id = None

        if available >= target:
            self.peaks = th.rebucket_peaks(self.full_peaks, start_frac, end_frac, target)
        else:
            density = target / max(1e-9, data_end - self.view_start)       # buckets per second needed
            d = getattr(self, "_detail", None)
            if d and d["t0"] <= self.view_start + 1e-9 and d["t1"] >= data_end - 1e-9 \
                    and d["density"] >= density * 0.95:
                length = d["t1"] - d["t0"]
                self.peaks = th.rebucket_peaks(d["peaks"], (self.view_start - d["t0"]) / length,
                                               (data_end - d["t0"]) / length, target)
                self._maybe_prefetch(density)
            else:
                if self.full_peaks:
                    self.peaks = th.rebucket_peaks(self.full_peaks, start_frac, end_frac, max(2, int(available)))
                gen = self._view_gen
                self._detail_after_id = self.canvas.after(
                    120, lambda: self._decode_detail_window(self.view_start, density, gen=gen))
        if render:
            self.render_waveform()

    def _detail_window(self, start, span):
        t0 = max(0.0, start - self.DETAIL_BEHIND * span)
        t1 = min(self.audio_duration, start + (1.0 + self.DETAIL_AHEAD) * span)
        return t0, t1

    def _maybe_prefetch(self, density):
        """Near the end of the decoded detail: decode the next stretch now,
        in the background, before the view (or the playhead) gets there."""
        d = self._detail
        span = min(self.view_end, self.audio_duration) - self.view_start
        if d["t1"] >= self.audio_duration - 1e-6 or getattr(self, "_detail_busy", False):
            return
        if self.view_end > d["t1"] - 0.5 * span:
            self._decode_detail_window(self.view_start, density, gen=None)

    def _decode_detail_window(self, start, density, gen=None):
        """Decode detail peaks for [start - 0.25 page, start + 2.75 pages] at
        `density` buckets/second in a worker thread, then store them as the
        detail cache and redraw if the current view can use them. gen=None
        marks a prefetch (kept even if the view has moved since)."""
        self._detail_after_id = None
        if gen is not None and gen != self._view_gen:
            return
        if getattr(self, "_detail_busy", False):
            # one decode at a time; the finished one re-checks the view
            self._detail_wanted = (start, density)
            return
        span = min(self.view_end, self.audio_duration) - self.view_start
        t0, t1 = self._detail_window(start, max(span, 1e-3))
        buckets = max(2, min(self.DETAIL_MAX_BUCKETS, int(density * (t1 - t0))))
        result = {}
        self._detail_busy = True

        def worker():
            try:
                result["peaks"] = th.decode_waveform_peaks(self.filepath, t0, t1 - t0, buckets)
            except Exception as exc:
                result["error"] = exc

        thread = threading.Thread(target=worker, daemon=True)
        thread.start()

        def poll():
            if thread.is_alive():
                self.canvas.after(60, poll)
                return
            self._detail_busy = False
            if result.get("peaks"):
                self._detail = {"t0": t0, "t1": t1, "peaks": result["peaks"],
                                "density": len(result["peaks"]) / max(1e-9, t1 - t0)}
                self._refresh_view_from_cache()      # uses the new detail if it fits the view
            elif "error" in result:
                debug(2, f"{{yellow}}waveform detail decode failed: {result['error']}")
            wanted = getattr(self, "_detail_wanted", None)
            self._detail_wanted = None
            if wanted and not result.get("peaks"):
                self._decode_detail_window(*wanted)

        self.canvas.after(60, poll)

    # ------------------------------------------------------------------ marks/tracks core
    def _mark_snapshot(self):
        return (copy.deepcopy(self.marks), copy.deepcopy(self.tracks), list(self.voices))

    def _one_step(self, fn):
        """Run fn (several mark edits) as one undo step, drawing the
        waveform and the card editor once at the end instead of after each
        edit (with dozens of cards, redrawing after every split made the
        window stop responding)."""
        self._batch_depth = getattr(self, "_batch_depth", 0) + 1
        try:
            self.canvas.configure(cursor="watch")
            self.canvas.update_idletasks()
        except (tk.TclError, AttributeError):
            pass
        try:
            result = fn()
        finally:
            self._batch_depth -= 1
            try:
                self.canvas.configure(cursor="")
            except (tk.TclError, AttributeError):
                pass
        if self._batch_depth == 0:
            self._mark_changed()
            self.render_waveform()
        return result

    def _mark_changed(self, record_history=True):
        """Marks/tracks changed: flag the tab as having unsaved changes
        (tab label "*"). They're written to the media file's combined
        "<stem>-tracked.json" by File > Save, auto-save, or the close/quit
        prompt -- all through tab.save_hook = save_marks_now. The audio
        file itself is never written. Without a tab (standalone use) they
        are saved immediately, as before."""
        if getattr(self, "_batch_depth", 0):
            record_history = False           # _one_step records the whole batch once
        # The unsaved flag comes first, so a failure in the bookkeeping
        # below (logged) can't leave a change looking saved.
        mark_dirty = getattr(self.tab, "mark_dirty", None) if self.tab is not None else None
        if callable(mark_dirty):
            mark_dirty()
        for step in ((self._push_mark_history,) if record_history else ()) + (self._sync_play_segment,):
            try:
                step()
            except Exception as exc:
                debug(1, f"{{red}}_mark_changed: {step.__name__} failed: {exc!r}")
        if not callable(mark_dirty):
            self.save_marks_now()

    def save_marks_now(self):
        """tab.save_hook: write marks/tracks to the sidecar cache -- after
        applying whatever is typed in the cards but not yet committed."""
        if self.panel is not None:
            self.panel.commit_pending()
        th.save_marks(self.filepath, self.marks, self.tracks, self.voices)
        self.remember_selection()
        if self.panel is not None and self.panel.has_pending():
            # still typing a time in a card: keep the tab marked unsaved
            # (tracked.py marks it clean right after this returns)
            try:
                self.canvas.after_idle(lambda: self._mark_tab_dirty())
            except tk.TclError:
                pass
        return True

    def _mark_tab_dirty(self):
        mark_dirty = getattr(self.tab, "mark_dirty", None) if self.tab is not None else None
        if callable(mark_dirty):
            mark_dirty()

    def show_time(self, t):
        """Scroll (not zoom) so time t is in view, if it isn't."""
        if t is None or self.audio_duration is None:
            return False
        span = self.view_end - self.view_start
        if self.view_start <= t <= self.view_end or span <= 0:
            return False
        new_start = max(0.0, min(self.audio_duration * self.OVERSHOOT_FACTOR - span, t - span * 0.05))
        self.view_start, self.view_end = new_start, new_start + span
        self._refresh_view_from_cache(render=False)
        return True

    def mark_at_playhead(self, track_id, pos, marks=None):
        """The mark of this track the playhead is in: a range while
        start <= pos < end; a point from its time until the next mark
        starts. None in a gap."""
        if pos is None:
            return None
        marks = self.track_marks(track_id) if marks is None else marks
        current = None
        for m in marks:
            if m["start"] > pos + 1e-9:
                break
            if m["type"] == "range" and m.get("end") is not None:
                current = m if pos < m["end"] else None
            else:
                current = m
        return current["id"] if current else None

    def _update_play_highlight(self, pos):
        """While playing, light up the card the playhead is in (when the
        text panel shows a track's cards)."""
        panel = self.panel
        if panel is None or getattr(panel, "mode", None) != "track" or not panel.track_id:
            return
        mid = None
        if pos is not None and self._play_state == "playing":
            mid = self.mark_at_playhead(panel.track_id, pos, panel.visible_marks(panel.track_id))
        panel.set_playing_mark(mid)

    def _sync_play_segment(self):
        """A card's mark is playing (or looping, or paused) and its times
        changed: play the new span -- the loop repeats the new start..end,
        and a position now outside it jumps to the new start."""
        mid = self._play_mark_id
        if mid is None or self._play_state == "stopped":
            return
        mark = self.mark_by_id(mid)
        if mark is None:
            return
        is_range = mark["type"] == "range" and mark.get("end") is not None
        start, end = mark["start"], (mark["end"] if is_range else None)
        if (start, end) == (self._play_seg_start, self._play_seg_end):
            return
        self._play_seg_start, self._play_seg_end = start, end
        self._play_origin = start
        if self._play_state == "playing":
            pos = self.current_play_position() or start
            if pos < start or (end is not None and pos >= end - 0.01):
                pos = start
            self._halt_engine()
            self.cursor_time = pos
            self._run_engine_from(pos)
        else:                   # paused: keep the cursor inside the span
            if self.cursor_time < start or (end is not None and self.cursor_time > end):
                self.cursor_time = start

    def _push_mark_history(self):
        views = self.__dict__.setdefault("_history_views", [None] * len(self._mark_history))
        del self._mark_history[self._mark_history_index + 1:]
        del views[self._mark_history_index + 1:]
        views.extend([None] * (len(self._mark_history) - len(views)))
        self._mark_history.append(self._mark_snapshot())
        views.append(self._current_view())
        max_len = self.UNDO_LIMIT + 1
        if len(self._mark_history) > max_len:
            cut = len(self._mark_history) - max_len
            del self._mark_history[:cut]
            del views[:cut]
        self._mark_history_index = len(self._mark_history) - 1

    def _current_view(self):
        if self.audio_duration is None or self.view_end <= self.view_start:
            return None
        return (self.view_start, self.view_end)

    def _restore_history_view(self, step):
        """Undo/redo: show the zoom and scroll position the step was made
        in, so the change being undone/redone is in view."""
        views = getattr(self, "_history_views", None) or []
        view = views[step] if 0 <= step < len(views) else None
        if view is None or self.audio_duration is None:
            return False
        start, end = view
        limit = self.audio_duration * self.OVERSHOOT_FACTOR
        if not (0.0 <= start < end <= limit + 1e-6):
            return False
        if (start, end) == (self.view_start, self.view_end):
            return False
        self.view_start, self.view_end = start, end
        self._refresh_view_from_cache(render=False)
        return True

    def can_undo_marks(self):
        return self._mark_history_index > 0

    def can_redo_marks(self):
        return self._mark_history_index < len(self._mark_history) - 1

    def undo_marks(self):
        if not self.can_undo_marks():
            return
        undone = self._mark_history_index
        self._mark_history_index -= 1
        self.marks, self.tracks, self.voices = copy.deepcopy(self._mark_history[self._mark_history_index])
        self._restore_history_view(undone)          # where the undone change was made
        self._keep_selection_if_present()
        self._hover = None
        self._mark_changed(record_history=False)
        self.render_waveform()

    def _keep_selection_if_present(self):
        """After undo/redo, keep the selection if that mark/track still
        exists (so the timing panel stays on the same track); otherwise
        fall back to the track the mark was in, or nothing."""
        if not self.selected:
            return
        kind, sel_id = self.selected
        if kind == "mark" and self.mark_by_id(sel_id):
            return
        if kind == "track" and self.track_by_id(sel_id):
            return
        track_id = getattr(self, "_last_panel_track", None)
        self.selected = ("track", track_id) if track_id and self.track_by_id(track_id) else None

    def redo_marks(self):
        if not self.can_redo_marks():
            return
        self._mark_history_index += 1
        self.marks, self.tracks, self.voices = copy.deepcopy(self._mark_history[self._mark_history_index])
        self._restore_history_view(self._mark_history_index)
        self._keep_selection_if_present()
        self._hover = None
        self._mark_changed(record_history=False)
        self.render_waveform()

    def _add_mark(self, mark_type, start, end, label="", track_id=None, source="user", record_history=True):
        mark = {
            "id": uuid.uuid4().hex[:8], "type": mark_type, "start": start, "end": end,
            "label": label, "track_id": track_id, "source": source,
        }
        self.marks.append(mark)
        self._mark_changed(record_history=record_history)
        return mark

    def _ensure_tracks_fit(self):
        """A new track band must be visible: if the waveform panel is too
        short for the waveform (60 px) + every track band, make it taller
        (the tab's sash), up to 75% of the window."""
        paned = getattr(self.tab, "paned", None) if self.tab is not None else None
        if paned is None:
            return False
        try:
            canvas_h = int(self.canvas.winfo_height())
            sash = int(paned.sashpos(0))
            window_h = int(self.canvas.winfo_toplevel().winfo_height())
        except (tk.TclError, TypeError, ValueError, AttributeError):
            return False
        need = 60 + self.STATUS_ROW_HEIGHT + len(self.tracks) * self.TRACK_HEIGHT + 4
        if canvas_h >= need:
            return False
        new = min(sash + (need - canvas_h), int(window_h * 0.75))
        if new <= sash:
            return False
        try:
            paned.sashpos(0, new)
            return True
        except tk.TclError:
            return False

    def _new_track(self, name, color=None, source="user", record_history=True):
        if color is None:
            color = self.TRACK_PALETTE[len(self.tracks) % len(self.TRACK_PALETTE)]
        track = {"id": uuid.uuid4().hex[:8], "name": name, "color": color, "source": source}
        self.tracks.append(track)
        self._mark_changed(record_history=record_history)
        try:
            self.canvas.after_idle(self._ensure_tracks_fit)   # after the new band is laid out
        except (tk.TclError, AttributeError):
            pass
        return track

    def delete_track(self, track, record_history=True):
        """Delete a track (a track dict, or a track id string) and every
        mark assigned to it. No confirmation prompt -- see _delete_track
        for the confirming UI wrapper."""
        track_id = track["id"] if isinstance(track, dict) else track
        self.marks = [m for m in self.marks if m.get("track_id") != track_id]
        self.tracks = [t for t in self.tracks if t["id"] != track_id]
        if self.selected:
            kind, sel_id = self.selected
            if (kind == "track" and sel_id == track_id) or (
                kind == "mark" and not any(m["id"] == sel_id for m in self.marks)
            ):
                self.selected = None
        if record_history:
            self._mark_changed()
        self.render_waveform()
        return track_id

    def _delete_track(self, track):
        n_marks = sum(1 for m in self.marks if m.get("track_id") == track["id"])
        warning = f"Delete track \"{track['name']}\"?"
        if n_marks:
            plural = "s" if n_marks != 1 else ""
            warning += f" This will also delete the {n_marks} timing mark{plural} inside it."
        if not messagebox.askyesno("Delete Track", warning):
            return
        self.delete_track(track)

    def _delete_mark(self, mark):
        self.marks = [m for m in self.marks if m["id"] != mark["id"]]
        if self.selected == ("mark", mark["id"]):
            self.selected = None
        self._mark_changed()
        self.render_waveform()

    def delete_mark_by_id(self, mark_id):
        """Delete a mark; if it was in a track, select the next card there
        (or the previous one if it was the last), else the track itself --
        so the track keeps the focus."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return False
        after = th.neighbor_mark(self.marks, mark, 1) or th.neighbor_mark(self.marks, mark, -1)
        track_id = mark.get("track_id")
        self._delete_mark(mark)
        if track_id is not None:
            self.selected = ("mark", after["id"]) if after else ("track", track_id)
            self.render_waveform()
        return True

    # ------------------------------------------------------------------ close
    UNASSIGNED_TRACK_NAME = "Unassigned marks"

    def before_close(self):
        """tab.before_close_hook: marks still in the work area (not in any
        track)? Offer to move them into a new track, delete them, or leave
        them for next time. Returns False if the user cancels the close.
        Also saves the selection if it changed since the last save."""
        if self.selection_needs_saving():
            self.remember_selection()
        loose = [m for m in self.marks if m.get("track_id") is None]
        if not loose:
            return True
        choice = self.ask_unassigned(len(loose))
        if choice == "cancel":
            return False
        if choice == "track":
            track = self._new_track(self.UNASSIGNED_TRACK_NAME, record_history=False)
            for m in loose:
                m["track_id"] = track["id"]
            self._mark_changed()
        elif choice == "delete":
            ids = {m["id"] for m in loose}
            self.marks = [m for m in self.marks if m["id"] not in ids]
            self._mark_changed()
        self.render_waveform()
        return True

    def ask_unassigned(self, count):
        """A small modal choice: "track" / "delete" / "leave" / "cancel"."""
        try:
            top = tk.Toplevel(self.canvas)
        except tk.TclError:
            return "leave"
        top.title("Unassigned timing marks")
        top.configure(bg="#f2f2f2")   # explicit colors: readable on dark desktop themes too
        top.transient(self.canvas.winfo_toplevel())
        result = {"choice": "cancel"}
        name = Path(self.filepath).name
        tk.Label(top, text=f"\u201c{name}\u201d has {count} timing mark{'s' if count != 1 else ''} "
                           "on the waveform that aren't in any track.\nWhat should happen to them?",
                 justify="left", padx=14, pady=10, fg="#1e1e1e", bg="#f2f2f2").pack(anchor="w")
        row = tk.Frame(top, padx=10, pady=8, bg="#f2f2f2")
        row.pack(fill="x")

        def pick(value):
            result["choice"] = value
            top.destroy()

        for text, value in (("Save into a new track", "track"), ("Delete them", "delete"),
                            ("Leave them for next time", "leave"), ("Cancel", "cancel")):
            tk.Button(row, text=text, command=lambda v=value: pick(v), padx=8, bg="#e2e2e2", fg="#1e1e1e",
                      activebackground="#cfe0ff", activeforeground="#1e1e1e", cursor="hand2").pack(side="left", padx=4)
        top.protocol("WM_DELETE_WINDOW", lambda: pick("cancel"))
        top.bind("<Escape>", lambda e: pick("cancel"))
        try:
            top.grab_set()
            top.wait_window()
        except tk.TclError:
            pass
        return result["choice"]

    def select_track_only(self, track_id):
        """Deselect any card/mark but keep showing that track's panel."""
        if self.track_by_id(track_id) and self.selected != ("track", track_id):
            self.selected = ("track", track_id)
            self.render_waveform()

    def mouse_busy(self):
        """True while a canvas drag (moving/resizing a mark, drawing a
        range, reordering a track) is in progress."""
        return bool(self._move_drag or self._track_drag
                    or (self._press_info and self._press_info.get("dragging")))

    def neighbor_time(self, mark_id, direction):
        """For the card snap buttons: the end of the previous mark
        (direction -1) or the start of the next one (+1) in the same track;
        with no neighbor, the start (0:00) or end of the audio."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return None
        other = th.neighbor_mark(self.marks, mark, direction)
        if other is None:
            return 0.0 if direction < 0 else self.audio_duration
        if direction < 0:
            return other["end"] if other.get("type") == "range" and other.get("end") is not None else other["start"]
        return other["start"]

    def _delete_all_marks(self):
        self.marks = []
        if self.selected and self.selected[0] == "mark":
            self.selected = None
        self._mark_changed()
        self.render_waveform()

    def _edit_mark_label(self, mark):
        new_label = simpledialog.askstring("Mark Label", "Label text:", initialvalue=mark["label"])
        if new_label is not None:
            mark["label"] = new_label.strip()
            self._mark_changed()
            self.render_waveform()

    def _clear_mark_label(self, mark):
        mark["label"] = ""
        self._mark_changed()
        self.render_waveform()

    def _set_mark_duration(self, mark):
        current = (mark["end"] - mark["start"]) if mark["type"] == "range" and mark.get("end") is not None else 0.0
        result = simpledialog.askfloat("Set Duration", "Duration (seconds):",
                                        initialvalue=round(current, 3), minvalue=0.01)
        if result is None:
            return
        duration = self.audio_duration or 0.0
        new_end = mark["start"] + result
        if duration:
            new_end = min(duration, new_end)
        mark["type"] = "range"
        mark["end"] = new_end
        self._mark_changed()
        self.render_waveform()

    def _rename_track(self, track):
        new_name = simpledialog.askstring("Rename Track", "Track name:", initialvalue=track["name"])
        if new_name and new_name.strip():
            track["name"] = new_name.strip()
            self._mark_changed()
            self.render_waveform()

    def _change_track_color(self, track):
        result = colorchooser.askcolor(color=track["color"], title="Track Color")
        if result and result[1]:
            track["color"] = result[1]
            self._mark_changed()
            self.render_waveform()

    def _prompt_new_track_for_mark(self, mark):
        self._prompt_new_track_for_marks([mark])

    def _prompt_new_track_for_marks(self, marks):
        """Dropped below the tracks: ask for a name; the marks go into the new track."""
        name = simpledialog.askstring("New Timing Track", "Track name:")
        if name and name.strip():
            track = self._new_track(name.strip())
            for mark in marks:
                mark["track_id"] = track["id"]
            self._mark_changed()
            self.render_waveform()

    # ------------------------------------------------------------------ lookups used by the timing panel
    def mark_by_id(self, mark_id):
        if mark_id is None:
            return None
        return next((m for m in self.marks if m["id"] == mark_id), None)

    def track_by_id(self, track_id):
        return next((t for t in self.tracks if t["id"] == track_id), None)

    def track_marks(self, track_id):
        return sorted((m for m in self.marks if m.get("track_id") == track_id),
                      key=lambda m: (m["start"], m.get("end") or m["start"], m["id"]))

    def selected_mark_id(self):
        if self.selected and self.selected[0] == "mark":
            return self.selected[1]
        return None

    def panel_track_id(self):
        """Which track the text panel should show: the selected track, or
        the track of the selected mark; None -> the normal info text."""
        if not self.selected:
            return None
        kind, sel_id = self.selected
        if kind == "track":
            track_id = sel_id if self.track_by_id(sel_id) else None
        else:
            mark = self.mark_by_id(sel_id)
            track_id = mark.get("track_id") if mark else None
        if track_id:
            self._last_panel_track = track_id
        return track_id

    def select_mark(self, mark_id, from_panel=False):
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return
        if self.selected == ("mark", mark_id):
            if from_panel:              # focus moved within the card, or back to it
                self.reveal_mark(mark_id)
            return
        self.selected = ("mark", mark_id)
        self._ensure_mark_visible(mark)
        self.render_waveform()

    def cursor_position(self):
        """The @cursor (it moves with playback while playing)."""
        pos = self.current_play_position()
        return self.cursor_time if pos is None else pos

    def play_mark_by_id(self, mark_id, loop=False):
        """Play (or with loop=True, loop) one mark's span from its start."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return
        self.selected = ("mark", mark_id)
        if self._play_state == "playing":
            self._halt_engine()
        self._play_state = "stopped"
        is_range = mark["type"] == "range" and mark.get("end") is not None
        self.start_play(loop=loop, segment=(mark["start"], mark["end"] if is_range else None), mark_id=mark_id)

    def toggle_mark_play(self, mark_id, loop=False, resume=False):
        """A timing card's Play/Pause button, like the main one: pause if
        this mark is playing; while paused, play it again from its start
        (Ctrl: resume from the paused spot); else start it (Shift: loop)."""
        mine = self._play_mark_id == mark_id and self._play_state != "stopped"
        if loop:
            self.play_mark_by_id(mark_id, loop=True)
        elif mine and self._play_state == "playing":
            self.pause_play()
        elif mine and self._play_state == "paused":
            if resume:
                self.start_play()
            else:
                self.play_mark_by_id(mark_id, loop=self._loop)
        else:
            self.play_mark_by_id(mark_id, loop=False)

    def mark_play_state(self, mark_id):
        """"playing" / "paused" / "stopped" for one mark's card button."""
        if self._play_mark_id != mark_id:
            return "stopped"
        return self._play_state

    # ------------------------------------------------------------------ edits used by the panel / menus
    def max_mark_time(self):
        """How far past the end of the audio a mark may reach: 10% (the
        same as zooming out past "fit"), e.g. to line up ranges without
        changing their durations."""
        if self.audio_duration is None:
            return float("inf")
        return self.audio_duration * self.OVERSHOOT_FACTOR

    def set_mark_times(self, mark_id, start, end):
        """Set a mark's start and end (end None -> point). Returns False
        (and changes nothing) if the values are out of range (marks may
        reach up to 10% past the end of the audio, see max_mark_time)."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return False
        limit = self.max_mark_time()
        if start is None or start < 0 or start > limit:
            return False
        if end is not None:
            if end > limit + 1e-6 or end - start < th.MIN_RANGE - 1e-9:
                return False
            mark["type"], mark["start"], mark["end"] = "range", float(start), float(end)
        else:
            mark["type"], mark["start"], mark["end"] = "point", float(start), None
        self._mark_changed()
        self.render_waveform()
        return True

    REST_GAP_TOLERANCE = 0.001      # marks closer than this count as touching

    def previous_in_track(self, mark_id):
        mark = self.mark_by_id(mark_id)
        if mark is None or mark.get("track_id") is None:
            return None
        in_track = self.track_marks(mark["track_id"])
        i = in_track.index(mark)
        return in_track[i - 1] if i > 0 else None

    def set_mark_start_joined(self, mark_id, start, mode="all"):
        """Set a mark's Start and make the previous mark in its track end
        right there (the card's <Join button) -- one undo step. mode
        "group": only if the two marks were touching; "all": always (a
        gap closes). The previous mark must keep at least the minimum
        length. False (nothing changed) if a time is invalid."""
        mark = self.mark_by_id(mark_id)
        if mark is None or start is None:
            return False
        prev = self.previous_in_track(mark_id)
        if mode == "group" and prev is not None:
            prev_end = prev["end"] if prev["type"] == "range" and prev.get("end") is not None else prev["start"]
            if abs(mark["start"] - prev_end) > self.REST_GAP_TOLERANCE:
                is_range = mark["type"] == "range" and mark.get("end") is not None
                return self.set_mark_times(mark_id, start, mark["end"] if is_range else None)
        is_range = mark["type"] == "range" and mark.get("end") is not None
        start = float(start)
        if start < 0 or start > self.max_mark_time() or (is_range and mark["end"] - start < th.MIN_RANGE - 1e-9):
            return False
        if prev is not None and start - prev["start"] < th.MIN_RANGE - 1e-9:
            return False
        mark["start"] = start
        if prev is not None:
            prev["type"], prev["end"] = "range", start
        self._mark_changed()
        self.render_waveform()
        return True

    def rest_followers(self, mark_id, mode="all"):
        """The marks that move with this one's End: "all" -> every later
        mark in the track; "group" -> only the ones that follow on without a
        gap (each starts where the one before ends, or earlier)."""
        mark = self.mark_by_id(mark_id)
        if mark is None or mark.get("track_id") is None:
            return []
        in_track = self.track_marks(mark["track_id"])
        followers = in_track[in_track.index(mark) + 1:]
        if mode not in ("group", "gap"):
            return followers
        edge = mark["end"] if mark["type"] == "range" and mark.get("end") is not None else mark["start"]
        chain = []
        for m in followers:
            if m["start"] - edge > self.REST_GAP_TOLERANCE:
                break
            chain.append(m)
            edge = max(edge, m.get("end") or m["start"])
        return chain

    def set_mark_end_shifting(self, mark_id, end, mode="all"):
        """Set a mark's End and move the following marks by the same
        amount (the card's rest button: mode "all" = every later mark in
        the track, "group" = up to the first gap) -- one undo step.
        In "group" mode the moving block stops where it touches the next
        mark (a further step then carries that one along too). Marks may
        be pushed up to 10% past the end of the audio (max_mark_time);
        beyond that they're squeezed against the limit (the End still
        changes). False (nothing changed) if End is invalid."""
        mark = self.mark_by_id(mark_id)
        if mark is None or end is None:
            return False
        followers = self.rest_followers(mark_id, mode)
        old_end = mark["end"] if mark["type"] == "range" and mark.get("end") is not None else mark["start"]
        limit = self.max_mark_time()
        end = min(float(end), limit)
        delta = end - old_end
        if followers and delta > 0 and mode in ("group", "gap"):
            in_track = self.track_marks(mark["track_id"])
            after = in_track[in_track.index(followers[-1]) + 1:]
            if after:
                block_end = max((m.get("end") or m["start"]) for m in followers)
                delta = min(delta, max(0.0, after[0]["start"] - block_end))
        if followers and delta < 0:
            delta = max(delta, -min(m["start"] for m in followers))
        end = old_end + delta
        if end - mark["start"] < th.MIN_RANGE - 1e-9:
            return False
        if abs(delta) < 1e-9:
            return True
        mark["type"], mark["end"] = "range", float(end)
        for m in followers:
            m["start"] = float(m["start"]) + delta
            if m.get("end") is not None:
                m["end"] = float(m["end"]) + delta
        if delta > 0 and limit != float("inf"):
            # squeeze anything pushed past the limit against it
            for m in sorted(followers, key=lambda x: x["start"], reverse=True):
                if m.get("end") is not None:
                    m["end"] = min(m["end"], limit)
                    m["start"] = min(m["start"], m["end"] - th.MIN_RANGE)
                    limit = min(limit, m["end"])
                else:
                    m["start"] = min(m["start"], limit)
        self._mark_changed()
        self.render_waveform()
        return True

    # ------------------------------------------------------------------ audio edges
    def edge_source(self, use_vocals=True):
        """The audio to look for edges in: the vocals stem (the default --
        cards are usually lyrics) when it's been separated and is current,
        else (or with use_vocals=False, Shift+click) the full mix."""
        if use_vocals and aa.stems_are_fresh(self.filepath):
            return str(aa.stem_paths(self.filepath)[0])
        return self.filepath

    def rise_time(self, t, use_vocals=True, direction=1):
        """Where a card's Start goes for the next/previous rising edge: the
        edge found by edge_time, minus the lead-in (Preferences, default
        0.15 s -- the sound usually starts a little before the detected
        foot). The search starts from t + lead-in, so repeated clicks step
        on to the next edge instead of finding the same one again."""
        lead = get_edge_lead_in()
        edge = self.edge_time(t + lead, "rise", use_vocals=use_vocals, direction=direction)
        return None if edge is None else max(0.0, edge - lead)

    def edge_time(self, t, kind, use_vocals=True, direction=1):
        """Time of the next (direction 1) or previous (-1) audio edge
        from t: kind "rise" = foot of a rising edge (an onset), "fall" =
        bottom of a falling edge. Looks at a few seconds at a time, up to
        ~20 s away. None if there's none (or the audio can't be read)."""
        if self.audio_duration is None:
            return None
        path = self.edge_source(use_vocals)
        buckets = int(round(th.EDGE_WINDOW_SEC / th.EDGE_BUCKET_SEC))
        step = th.EDGE_WINDOW_SEC - th.EDGE_CONTEXT_SEC
        if direction > 0:
            start = max(0.0, t - th.EDGE_CONTEXT_SEC)
        else:
            start = max(0.0, t + th.EDGE_CONTEXT_SEC - th.EDGE_WINDOW_SEC)
        for _ in range(th.EDGE_MAX_LOOKS):
            if start >= self.audio_duration:
                break
            length = min(th.EDGE_WINDOW_SEC, self.audio_duration - start)
            try:
                peaks = th.decode_waveform_peaks(path, start, length,
                                                 max(20, int(buckets * length / th.EDGE_WINDOW_SEC)))
            except Exception as exc:
                debug(2, f"{{red}}edge search: {exc}")
                return None
            if not peaks:
                return None
            env, bucket = th.edge_envelope(peaks), length / len(peaks)
            if direction > 0:
                found = th.find_edge(env, start, bucket, t, kind)
            else:
                found = th.find_prev_edge(env, start, bucket, t, kind)
            if found is not None:
                return max(0.0, min(found, self.audio_duration))
            if direction > 0:
                start += step
            else:
                if start <= 0.0:
                    break
                start = max(0.0, start - step)
        return None

    def set_mark_label(self, mark_id, label):
        """Set a card's text. Lyrics entirely in parentheses on a card with
        no voice yet get the parentheses voice (see paren_voice_for)."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return False
        mark["label"] = label.strip()
        if mark["label"] and not mark.get("voices") and \
                th.in_parentheses(mark["label"], (0, len(mark["label"]))):
            mark["voices"] = [self.paren_voice_for(mark)]
        self._mark_changed()
        self.render_waveform()
        return True

    def split_mark_by_id(self, mark_id, text_index=None, at_time=None):
        """Split a mark in two (see timing_helpers.plan_split). With no
        explicit at_time, the playback/Ctrl+click cursor is used if it
        falls inside the range. Returns False if it couldn't be split."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return False
        if at_time is None:
            at_time = self.cursor_position()
        plan = th.plan_split(mark, at_time=at_time, text_index=text_index)
        if plan is None:
            return False
        (ls, le, ltext), (rs, re_, rtext) = plan["left"], plan["right"]
        pieces, before_ids = mark.pop("pieces", None), {m["id"] for m in self.marks}
        label = mark.get("label") or ""
        lv = self._voices_for_piece(mark, label, th.find_span(label, ltext, 0))
        rv = self._voices_for_piece(mark, label, th.find_span(label, rtext, len(ltext)))
        mark["start"], mark["end"], mark["label"] = ls, le, ltext
        mark["type"] = "range" if le is not None else "point"
        new = {
            "id": uuid.uuid4().hex[:8], "type": "range" if re_ is not None else "point",
            "start": rs, "end": re_, "label": rtext, "track_id": mark.get("track_id"),
            "source": mark.get("source", "user"),
        }
        for m_, v_ in ((mark, lv), (new, rv)):
            if v_:
                m_["voices"] = v_
            else:
                m_.pop("voices", None)
        self.marks.append(new)
        self._carry_pieces(mark, before_ids, pieces)
        self._mark_changed()
        self.render_waveform()
        return True

    def split_mark_into(self, mark_id, spans):
        """Split a mark into several at these character spans of its label
        (a phrase selection, or every word), timing each piece by its word
        weights -- see timing_helpers.plan_pieces. The first piece keeps the
        mark's id and stays selected. One undo step."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return False
        plan = th.plan_pieces(mark, spans)
        if not plan:
            return False
        label = mark.get("label") or ""
        piece_spans = [(a, b) for a, b in spans if label[a:b].strip()]
        voices = [self._voices_for_piece(mark, label, sp) for sp in piece_spans]
        if len(voices) != len(plan):
            voices = [list(mark.get("voices") or [])] * len(plan)
        pieces, before_ids = mark.pop("pieces", None), {m["id"] for m in self.marks}
        (s0, e0, t0), rest = plan[0], plan[1:]
        mark["start"], mark["end"], mark["label"] = s0, e0, t0
        mark["type"] = "range" if e0 is not None else "point"
        if voices[0]:
            mark["voices"] = voices[0]
        else:
            mark.pop("voices", None)
        for (s1, e1, t1), v1 in zip(rest, voices[1:]):
            piece = {
                "id": uuid.uuid4().hex[:8], "type": "range" if e1 is not None else "point",
                "start": s1, "end": e1, "label": t1, "track_id": mark.get("track_id"),
                "source": mark.get("source", "user"),
            }
            if v1:
                piece["voices"] = v1
            self.marks.append(piece)
        self._carry_pieces(mark, before_ids, pieces)
        self.selected = ("mark", mark_id)
        self._mark_changed()
        self.render_waveform()
        return True

    def unmerge_mark_by_id(self, mark_id):
        """Split a merged card back into the cards it was merged from
        (th.unmerge_plan): their own times and texts when nothing changed
        since; otherwise fitted to the card as it is now. One undo step.
        Returns (number of cards, how) or (0, "")."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return 0, ""
        plan, how = th.unmerge_plan(mark)
        if not plan:
            return 0, ""
        first, rest = plan[0], plan[1:]
        mark.pop("pieces", None)
        mark["start"], mark["end"], mark["label"] = first["start"], first.get("end"), first.get("label", "")
        mark["type"] = "range" if first.get("end") is not None else "point"
        if first.get("voices"):
            mark["voices"] = list(first["voices"])
        else:
            mark.pop("voices", None)
        for p in rest:
            piece = {"id": uuid.uuid4().hex[:8], "type": "range" if p.get("end") is not None else "point",
                     "start": p["start"], "end": p.get("end"), "label": p.get("label", ""),
                     "track_id": mark.get("track_id"), "source": mark.get("source", "user")}
            if p.get("voices"):
                piece["voices"] = list(p["voices"])
            self.marks.append(piece)
        self.selected = ("mark", mark_id)
        self._mark_changed()
        self.render_waveform()
        notes = {"exact": "", "moved": " (moved with the card)",
                 "text": " (edited text shared out)", "moved+text": " (fitted to new times; edited text shared out)"}
        self.play_status_var.set(f"Unmerged into {len(plan)} cards{notes.get(how, '')}")
        return len(plan), how

    def _carry_pieces(self, mark, before_ids, pieces):
        """After a merged card was split by hand, each part keeps the
        remembered pieces within its own span (so it can still be unmerged)."""
        if not pieces:
            return
        parts = [mark] + [m for m in self.marks if m["id"] not in before_ids]
        for part in parts:
            end = part["end"] if part.get("end") is not None else part["start"]
            kept = th.pieces_for_span(pieces, part["start"], end)
            if kept:
                part["pieces"] = kept
            else:
                part.pop("pieces", None)

    def merge_mark_by_id(self, mark_id, direction=1, pool=None):
        """Merge a mark with its next (+1) / previous (-1) neighbor in the
        same track (or the unassigned marks) into one range. pool: only
        these marks count as neighbors (the card editor passes the cards
        its Show: filter shows, so hidden cards are skipped)."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return False
        other = th.neighbor_mark(self.marks if pool is None else pool, mark, direction)
        if other is None:
            return False
        start, end, label = th.merged_fields(mark, other)
        if end - start < th.MIN_RANGE:
            return False
        mark["pieces"] = th.merged_pieces(mark, other)      # for Unmerge later
        mark["start"], mark["end"], mark["label"], mark["type"] = start, end, label, "range"
        voices = th.merge_voice_lists(mark.get("voices"), other.get("voices"))
        if voices:
            mark["voices"] = voices
        self.marks = [m for m in self.marks if m["id"] != other["id"]]
        self.selected = ("mark", mark["id"])
        self._mark_changed()
        self.render_waveform()
        return True

    # ------------------------------------------------------------------ voices
    def paren_voice_for(self, mark):
        """The voice for a card's lyrics in parentheses (backing vocals):
        the voice numbered one past the card's own "voice N" (a card with
        no numbered voice counts as voice 1 -> "voice 2")."""
        name = th.paren_voice_name(mark.get("voices"))
        if name not in self.voices:
            self.voices.append(name)
        return name

    def _voices_for_piece(self, mark, label, span):
        """Voices for a piece of a split card: its lyrics all in
        parentheses -> the parentheses voice (paren_voice_for), else the
        card's own voices."""
        if span is not None and th.in_parentheses(label, span):
            return [self.paren_voice_for(mark)]
        return list(mark.get("voices") or [])

    def mark_voices(self, mark_id):
        mark = self.mark_by_id(mark_id)
        return list(mark.get("voices") or []) if mark else []

    def set_mark_voices(self, mark_id, voices):
        """Assign exactly these voices to a mark (one undo step)."""
        mark = self.mark_by_id(mark_id)
        if mark is None:
            return False
        voices = th.merge_voice_lists(voices)
        if voices == (mark.get("voices") or []):
            return True
        for v in voices:
            if v not in self.voices:
                self.voices.append(v)
        if voices:
            mark["voices"] = voices
        else:
            mark.pop("voices", None)
        self._mark_changed()
        self.render_waveform()
        return True

    def toggle_mark_voice(self, mark_id, voice):
        current = self.mark_voices(mark_id)
        if voice in current:
            current.remove(voice)
        else:
            current.append(voice)
        # keep the file's voice order, so cards list their voices consistently
        return self.set_mark_voices(mark_id, [v for v in self.voices if v in current]
                                    + [v for v in current if v not in self.voices])

    def default_voice_name(self):
        return th.next_voice_name(self.voices)

    def add_voice(self, name=None, mark_id=None):
        """Create a voice ("voice N" unless a name is given) and, with
        mark_id, assign it to that mark -- together one undo step. An
        existing name is simply reused. Returns the name."""
        name = (name or "").strip() or self.default_voice_name()
        if name not in self.voices:
            self.voices.append(name)
        mark = self.mark_by_id(mark_id) if mark_id else None
        if mark is not None and name not in (mark.get("voices") or []):
            mark["voices"] = (mark.get("voices") or []) + [name]
        self._mark_changed()
        self.render_waveform()
        return name

    def ask_new_voice(self, mark_id=None):
        """New voice on the fly: a name prompt prefilled with "voice N"
        (just press Enter to take it, or type another name)."""
        default = self.default_voice_name()
        try:
            name = simpledialog.askstring("New Voice", "Voice name:", initialvalue=default,
                                          parent=self.canvas.winfo_toplevel())
        except tk.TclError:
            name = None
        if name is None:
            return None
        return self.add_voice(name.strip() or default, mark_id=mark_id)

    def rename_voice(self, old, new):
        new = (new or "").strip()
        if not new or old not in self.voices or new == old:
            return False
        if new in self.voices:          # renaming onto another voice merges them
            self.voices.remove(old)
        else:
            self.voices[self.voices.index(old)] = new
        for m in self.marks:
            if old in (m.get("voices") or []):
                m["voices"] = th.merge_voice_lists([new if v == old else v for v in m["voices"]])
        self._mark_changed()
        self.render_waveform()
        return True

    def ask_rename_voice(self, old):
        try:
            new = simpledialog.askstring("Rename Voice", f"New name for \u201c{old}\u201d:", initialvalue=old,
                                         parent=self.canvas.winfo_toplevel())
        except tk.TclError:
            new = None
        return self.rename_voice(old, new) if new else False

    def delete_voice(self, name):
        """Remove a voice name and take it off every mark."""
        if name not in self.voices:
            return False
        self.voices.remove(name)
        for m in self.marks:
            if name in (m.get("voices") or []):
                rest = [v for v in m["voices"] if v != name]
                if rest:
                    m["voices"] = rest
                else:
                    m.pop("voices", None)
        self._mark_changed()
        self.render_waveform()
        return True

    def voice_usage(self, name):
        return sum(1 for m in self.marks if name in (m.get("voices") or []))

    def fill_voice_menu(self, menu, mark_id):
        """The voices of one mark as check items, then New / Rename /
        Delete voice. Shared by the waveform's right-click menu and the
        card's Voice \u25be button."""
        try:
            menu.delete(0, "end")
        except tk.TclError:
            pass
        current = self.mark_voices(mark_id)
        self._voice_vars = {}
        all_var = tk.BooleanVar(value=not current)
        self._voice_vars[None] = all_var
        menu.add_checkbutton(label="All voices", variable=all_var, onvalue=True, offvalue=False,
                             command=lambda: self.set_mark_voices(mark_id, []))
        for v in self.voices:
            var = tk.BooleanVar(value=v in current)
            self._voice_vars[v] = var
            menu.add_checkbutton(label=v, variable=var, onvalue=True, offvalue=False,
                                 command=lambda name=v: self.toggle_mark_voice(mark_id, name))
        if self.voices:
            menu.add_separator()
        menu.add_command(label=f"New voice ({self.default_voice_name()} or a name)...",
                         command=lambda: self.ask_new_voice(mark_id))
        if self.voices:
            rename = tk.Menu(menu, tearoff=False, bg="#ffffff", fg="#1e1e1e")
            delete = tk.Menu(menu, tearoff=False, bg="#ffffff", fg="#1e1e1e")
            for v in self.voices:
                rename.add_command(label=v, command=lambda name=v: self.ask_rename_voice(name))
                n = self.voice_usage(v)
                delete.add_command(label=f"{v}  ({n} mark{'s' if n != 1 else ''})",
                                   command=lambda name=v: self.delete_voice(name))
            menu.add_cascade(label="Rename voice", menu=rename)
            menu.add_cascade(label="Delete voice", menu=delete)

    # ------------------------------------------------------------------ info text (text panel)
    def set_info_text(self, styled):
        self.info_text = styled

    def append_info(self, styled):
        """Add a line to the tab's info text (shown whenever no timing
        track is selected)."""
        self._progress_len = 0                  # a progress line above stays
        self.info_text += styled
        if self.panel is not None:
            self.panel.append_info(styled)

    def progress_info(self, styled):
        """A progress line that replaces the previous progress line (the
        same job's percentages update in place)."""
        n = getattr(self, "_progress_len", 0)
        if n:
            self.info_text = self.info_text[:-n]
        self.info_text += styled
        self._progress_len = len(styled)
        if self.panel is not None and hasattr(self.panel, "replace_progress"):
            self.panel.replace_progress(styled)

    # ------------------------------------------------------------------ Ctrl+click cursor
    def _on_ctrl_press(self, event):
        """Ctrl+click: on a mark in a track band, add it to / remove it from
        the selection; anywhere else, move the @cursor."""
        if self.audio_duration is None or self.view_end <= self.view_start:
            return "break"
        zone, target = self._track_zone_at_y(event.y)
        if zone == "track" and not self._track_label_hit(target, event.x, event.y):
            pool = [m for m in self.marks if m.get("track_id") == target]
            hit, _edge = self._mark_and_edge_at_x(event.x, pool=pool)
            if hit is not None:
                self._ctrl_selecting = True
                self.extend_selection(hit, toggle=True)
                return "break"
        self._ctrl_selecting = False
        self._set_cursor(self._time_at_x(event.x))
        return "break"

    def _on_ctrl_drag(self, event):
        if self.audio_duration is None or self.view_end <= self.view_start \
                or getattr(self, "_ctrl_selecting", False):
            return "break"
        self._set_cursor(self._time_at_x(event.x), seek_playing=False)
        return "break"

    def _set_cursor(self, t, seek_playing=True):
        """Ctrl+click: move the @cursor (seeking playback if playing)."""
        if self._play_state == "playing" and not seek_playing:
            return
        self.seek_to(t)

    # ------------------------------------------------------------------ stem regions
    def _set_regions(self, regions):
        """Keep the analyzed regions, and use them smoothed: changes shorter
        than the "stem_min_seconds" preference are merged away."""
        self._raw_regions = list(regions or [])
        self.regions = aa.smooth_regions(self._raw_regions, get_stem_min_seconds())
        self._region_starts = [r["start"] for r in self.regions]
        self._update_legend()

    def resmooth_regions(self):
        """Re-apply the smoothing preference (after it changes)."""
        self._set_regions(getattr(self, "_raw_regions", self.regions))
        if self.regions:
            self._report_regions()
        self.render_waveform()

    def _region_kind_at(self, t):
        if not self.regions:
            return None
        i = bisect.bisect_right(self._region_starts, t) - 1
        if 0 <= i < len(self.regions):
            return self.regions[i]["kind"]
        return None

    def _report_regions(self, elapsed=None, reused=None):
        if not self.regions:
            return
        counts = aa.region_counts(self.regions)
        secs = aa.region_seconds(self.regions)
        how = ""
        if reused is True:
            how = " (from cached stems)"
        elif reused is False:
            how = " (new stems)"
        msg = (
            f"\n{{green}}Stem regions{how} (changes under {get_stem_min_seconds():g}s merged)\n"
            f"{{blue}}  vocal-only regions:     {{cyan}}{counts['vocal']:4d}  ({th.format_time(secs['vocal'])})\n"
            f"{{blue}}  instrumental-only:      {{cyan}}{counts['novocal']:4d}  ({th.format_time(secs['novocal'])})\n"
            f"{{blue}}  mixed regions:          {{cyan}}{counts['mixed']:4d}  ({th.format_time(secs['mixed'])})\n"
            f"{{blue}}  silent regions:         {{cyan}}{counts['silent']:4d}  ({th.format_time(secs['silent'])})\n"
        )
        if elapsed is not None:
            msg += f"{{blue}}  elapsed: {{cyan}}{elapsed:.1f}s\n"
        self.append_info(msg)

    def _set_analysis_busy(self, what):
        """A long job starts (what) / ends (None). While it runs, the text
        panel is shown (the card editor would hide its progress): a selected
        track or card is deselected and selected again afterwards."""
        if what and not self._analysis_busy:
            self._progress_len = 0
            if self.selected and (self.selected[0] == "track" or self.panel_track_id()):
                self._sel_before_busy = (self.selected, list(getattr(self, "_multi", [])))
                self.selected = None
                self.render_waveform()
        elif not what and self._analysis_busy:
            saved = getattr(self, "_sel_before_busy", None)
            self._sel_before_busy = None
            if saved and self.selected is None:
                (kind, ident), multi = saved
                if (kind == "track" and self.track_by_id(ident)) or (kind == "mark" and self.mark_by_id(ident)):
                    self.selected = (kind, ident)
                    self._multi = [i for i in multi if self.mark_by_id(i)]
                    self.render_waveform()
        self._analysis_busy = what
        state = "disabled" if what else "normal"
        for btn in (self.stems_btn, self.transcribe_btn, self.model_btn, self.mood_btn,
                    getattr(self, "beats_btn", None), getattr(self, "structure_btn", None)):
            if btn is None:
                continue
            try:
                btn.configure(state=state)
            except tk.TclError:
                pass

    def _show_text_panel(self):
        """Make sure the text panel (not the card editor) is showing, so a
        message just added there is seen: deselects a selected track/card.
        Used for errors and "nothing made" results -- before this, a job's
        end re-selected the card and its message stayed hidden."""
        if self.selected and (self.selected[0] == "track" or self.panel_track_id()):
            self.selected = None
            self._multi = []
            self.render_waveform()

    def _run_in_thread(self, work, done, progress_prefix=""):
        """Run work(progress) in a thread; call done(result, error, elapsed)
        on the UI thread. progress(msg) may be called from the thread."""
        result = {}
        last = {"msg": None}
        t0 = time.time()

        def progress(msg):
            last["msg"] = msg

        def worker():
            try:
                result["value"] = work(progress)
            except Exception as exc:
                result["error"] = exc

        thread = threading.Thread(target=worker, daemon=True)
        thread.start()
        shown = {"msg": None}

        def poll():
            msg = last["msg"]
            if msg and msg != shown["msg"]:
                shown["msg"] = msg
                self.analysis_status_var.set(f"{progress_prefix}{msg}"[:70])
                if "%" in msg:
                    self.progress_info(f"{{cyan}}  {progress_prefix}{msg}\n")
            if thread.is_alive():
                self.canvas.after(150, poll)
                return
            done(result.get("value"), result.get("error"), time.time() - t0)

        self.canvas.after(150, poll)

    def run_stem_analysis(self, force=None, then=None):
        """Separate stems (or reuse the cached WAVs) and color the waveform.
        `then` is called afterwards (used by Transcribe)."""
        if force is None:
            force = getattr(self, "_force_stems", False)
            self._force_stems = False
        if self._analysis_busy or self.audio_duration is None:
            return
        if not aa.stems_are_fresh(self.filepath) and not aa.demucs_available():
            self.append_info("\n{yellow}Stem separation needs demucs (not installed). "
                             "Use the \u26a0 Install button in the upper right corner.\n")
            self.analysis_status_var.set("demucs not installed")
            if then:
                then()
            return
        if force and not aa.demucs_available():
            force = False
        self._set_analysis_busy("stems")
        self.append_info("\n{yellow}Analyzing stems in the background...\n")
        duration = self.audio_duration
        n_bins = max(th.WAVEFORM_CACHE_RESOLUTION, len(self.full_peaks))

        def work(progress):
            return aa.analyze_stems(self.filepath, duration, n_bins, progress, force=force)

        def done(value, error, elapsed):
            self._set_analysis_busy(None)
            if error is not None:
                self.analysis_status_var.set("Stems failed")
                self.append_info(f"\n{{red}}Stem analysis error: " + _explained(error, "Stem separation") + "\n")
                debug(1, f"{{red}}waveform_tab stems failed: {error}")
                self._show_text_panel()
            else:
                regions, reused = value
                self._set_regions(regions)
                th.save_regions(self.filepath, self._raw_regions)
                self.analysis_status_var.set("Stems ready")
                self._report_regions(elapsed, reused)
                self.render_waveform()
                debug(2, f"{{green}}waveform_tab stems: {len(regions)} regions in {elapsed:.1f}s")
            if then:
                then()

        self._run_in_thread(work, done)

    STEM_TRACK_NAMES = {"vocal": "Vocals", "novocal": "Instrumental", "mixed": "Mixed", "silent": "Silence"}
    STEM_COMBOS = (("Vocal or Mixed", ("vocal", "mixed"), "vocal"),
                   ("Instrumental or Mixed", ("novocal", "mixed"), "novocal"))

    def _legend_kind_at(self, x, y):
        layout = self._track_layout()
        if not (layout["row_top"] <= y < layout["track_top"]):
            return None
        for x0, x1, kind in getattr(self, "_legend_hits", []):
            if x0 <= x <= x1:
                return kind
        return None

    def pick_stem_color(self, kind):
        """Open the stem color picker for one kind: the waveform previews
        the color live while the sliders move; OK keeps it (saved as the
        "stem_colors" preference), Cancel restores the previous color."""
        original = self.region_colors.get(kind, REGION_COLORS.get(kind, "#888888"))
        picker = StemColorPicker(self.canvas, f"Color for {STEM_LABELS.get(kind, kind)} stem regions", original,
                                 on_change=lambda c: self._preview_stem_color(kind, c),
                                 on_done=lambda c: self._finish_stem_color(kind, original, c))
        self._color_picker = picker
        return picker

    def _preview_stem_color(self, kind, color):
        self.region_colors[kind] = color
        self._last_status_drawn = None
        if getattr(self, "_preview_after", None) is None:     # at most ~30 redraws/s while dragging
            def redraw():
                self._preview_after = None
                self.render_waveform()
            try:
                self._preview_after = self.canvas.after(30, redraw)
            except tk.TclError:
                self._preview_after = None

    def _finish_stem_color(self, kind, original, color):
        self._color_picker = None
        if color:
            self.set_stem_color(kind, color)
        else:
            self.region_colors = stem_colors()                # Cancel: back to the saved colors
            self.region_colors[kind] = stem_colors().get(kind, original)
            self._last_status_drawn = None
            self.render_waveform()

    def set_stem_color(self, kind, color):
        saved = dict(get_preference("stem_colors", {}) or {})
        saved[kind] = color.lower()
        set_preference("stem_colors", saved)
        self.region_colors = stem_colors()
        self._last_status_drawn = None
        self.render_waveform()

    def reset_stem_colors(self):
        set_preference("stem_colors", {})
        self.region_colors = stem_colors()
        self._last_status_drawn = None
        self.render_waveform()

    def stem_region_counts(self):
        return aa.region_counts(self.regions) if self.regions else {}

    def _fill_stems_menu(self):
        """Rebuilt each time the Stems \u25be menu opens."""
        menu = self.stems_menu
        try:
            menu.delete(0, "end")
        except tk.TclError:
            pass
        counts = self.stem_region_counts()
        kinds = [k for k in aa.KINDS if counts.get(k)]
        if not kinds:
            menu.add_command(label="No stem regions yet \u2013 run Stems first", state="disabled")
        else:
            here = self._region_at(self.cursor_position() or 0.0)
            if here is not None:
                name = self.STEM_TRACK_NAMES.get(here["kind"], here["kind"])
                menu.add_command(
                    label="New range from @cursor",
                    command=self.range_from_current_stem)
                menu.add_separator()
            menu.add_command(label="New timing track from:", state="disabled")
            for kind in kinds:
                menu.add_command(label=f"   {self.STEM_TRACK_NAMES[kind]} ({counts[kind]} regions)",
                                 command=lambda k=kind: self.create_stem_tracks([k]))
            for name, combo, _color_kind in self.STEM_COMBOS:
                n = len(aa.regions_for_kinds(self.regions, combo, self._merge_var.get()))
                menu.add_command(label=f"   {name} ({n} ranges)", state="normal" if n else "disabled",
                                 command=lambda nm=name, cb=combo: self.create_combined_stem_track(nm, cb))
            menu.add_checkbutton(label="   Merge touching regions of different stems",
                                 variable=self._merge_var,
                                 command=self._menu_option(self.stems_menu_btn, menu, self._on_merge_toggled))
            menu.add_separator()
            menu.add_command(label=f"All non-empty stems ({len(kinds)} tracks)",
                             command=lambda: self.create_stem_tracks(kinds))
        menu.add_separator()
        menu.add_command(label="Re-run separation", state="disabled" if self._analysis_busy else "normal",
                         command=lambda: self.run_stem_analysis(force=True))
        menu.add_command(label="Reset stem colors", command=self.reset_stem_colors)

    def _region_at(self, t):
        if not self.regions:
            return None
        i = bisect.bisect_right(self._region_starts, t) - 1
        return self.regions[i] if 0 <= i < len(self.regions) else None

    def range_from_current_stem(self):
        """A new (unassigned) range spanning the stem region under the
        @cursor; it's selected so it can be dragged into a track."""
        region = self._region_at(self.cursor_position() or 0.0)
        if region is None:
            return None
        mark = self._add_mark("range", region["start"], region["end"])
        self.selected = ("mark", mark["id"])
        self.render_waveform()
        return mark

    def _on_merge_toggled(self):
        set_preference("stem_track_merge", bool(self._merge_var.get()))

    def create_combined_stem_track(self, name, kinds, merge=None):
        """One track from several stem kinds (e.g. vocal or mixed). With
        merge (the menu's checkbox), touching regions become one range."""
        if merge is None:
            merge = bool(self._merge_var.get())
        spans = aa.regions_for_kinds(self.regions, set(kinds), merge)
        if not spans:
            return None
        color_kind = next((ck for nm, _k, ck in self.STEM_COMBOS if nm == name), kinds[0])
        track = self._new_track(name, color=self.region_colors.get(color_kind), source="stems",
                                record_history=False)
        for start, end in spans:
            self._add_mark("range", start, end, track_id=track["id"], source="stems", record_history=False)
        self._mark_changed()
        self.selected = ("track", track["id"])
        self.render_waveform()
        self.append_info(f"{{green}}Created track from stems: {name} ({len(spans)} ranges)\n")
        return track

    def create_stem_tracks(self, kinds):
        """One timing track per stem kind, with a range mark per region of
        that kind, in the region's color. One undo step for the lot."""
        created = []
        for kind in kinds:
            regions = [r for r in self.regions if r.get("kind") == kind]
            if not regions:
                continue
            track = self._new_track(self.STEM_TRACK_NAMES.get(kind, kind), color=self.region_colors.get(kind),
                                    source="stems", record_history=False)
            for r in regions:
                self._add_mark("range", r["start"], r["end"], track_id=track["id"], source="stems",
                               record_history=False)
            created.append(track)
        if created:
            self._mark_changed()      # a single undo step
            self.selected = ("track", created[0]["id"])
            self.render_waveform()
            self.append_info("{green}Created track(s) from stems: "
                             + ", ".join(f"{t['name']}" for t in created) + "\n")
        return created

    def run_genre_mood(self, force=None):
        """Genre / mood estimate in the background; the result goes to the
        text panel and is cached with the file. A cached result is reused
        (just shown again) until the audio file's timestamp changes, unless
        forced (Shift+click on Mood)."""
        if force is None:
            force = getattr(self, "_force_mood", False)
            self._force_mood = False
        if self._analysis_busy or self.audio_duration is None:
            return
        if not force:
            cached = th.load_genre_mood(self.filepath)
            if cached is not None:
                self._report_genre_mood(cached, cached=True)
                return
        if not aa.genre_mood_available():
            messagebox.showinfo("Genre / mood", "This needs librosa, which isn't installed.\n\n"
                                                "Use the \u26a0 Install button in the upper right corner.")
            return
        lyrics = " ".join(m.get("label", "") for m in self.marks if m.get("label"))
        self._set_analysis_busy("mood")
        self.append_info("\n{yellow}Estimating genre and mood in the background...\n")

        def work(progress):
            return aa.estimate_genre_mood(self.filepath, lyrics, progress)

        def done(value, error, elapsed):
            self._set_analysis_busy(None)
            if error is not None:
                self.analysis_status_var.set("Genre/mood failed")
                self.append_info(f"{{red}}Genre/mood error: " + _explained(error, "The genre/mood estimate") + "\n")
                self._show_text_panel()
                return
            th.save_genre_mood(self.filepath, value)
            self._report_genre_mood(value, elapsed)

        self._run_in_thread(work, done)

    def _report_genre_mood(self, value, elapsed=None, cached=False):
        self.genre_mood = value
        self.analysis_status_var.set(f"{value['genre']} \u00b7 {value['mood']}")
        alts = ", ".join(f"{g} ({c:.0%})" for g, c in value.get("alternatives", []))
        palette = ", ".join(f"{name} {hexc}" for hexc, name in value.get("palette", []))
        msg = (f"\n{{green}}Genre / mood estimate (rule-based guess)\n"
               f"{{blue}}  genre: {{cyan}}{value['genre']} ({value['confidence']:.0%})\n")
        if alts:
            msg += f"{{blue}}  also possible: {{cyan}}{alts}\n"
        msg += (f"{{blue}}  mood: {{cyan}}{value['mood']}  "
                f"{{blue}}(energy {value['energy']:.2f}, brightness {value['valence']:.2f}, "
                f"tempo ~{value['tempo']:.0f} BPM)\n"
                f"{{blue}}  mood palette: {{cyan}}{palette}\n")
        if elapsed is not None:
            msg += f"{{blue}}  elapsed: {{cyan}}{elapsed:.1f}s\n"
        if cached:
            msg += "{blue}  (cached result -- Shift+click Mood to re-run)\n"
        self.append_info(msg)

    def _auto_stems(self):
        """On load: show cached regions, or start analysis if it can run
        without user interaction (cached stems, or demucs installed) --
        same as the old audio tab, which ran demucs automatically."""
        self._update_legend()
        cached_mood = th.load_genre_mood(self.filepath)
        if cached_mood is not None:
            self._report_genre_mood(cached_mood, cached=True)
        if self.regions:
            self.analysis_status_var.set("Stems ready (cached)")
            self._report_regions()
            return
        if aa.stems_are_fresh(self.filepath) or aa.demucs_available():
            self.canvas.after(200, self.run_stem_analysis)

    # ------------------------------------------------------------------ transcription
    def _model_choices(self):
        auto = f"auto ({aa.default_whisper_model()})"
        return [auto] + aa.WHISPER_MODELS

    def _refresh_model_combo(self):
        """(Re)build the Whisper model menu on the Transcribe \u25be button."""
        choices = self._model_choices()
        saved = get_preference("whisper_model", "auto")
        self.model_var.set(saved if saved in aa.WHISPER_MODELS else choices[0])
        menu = self.model_menu
        try:
            menu.delete(0, "end")
        except tk.TclError:
            pass
        menu.add_command(label="Whisper model", state="disabled")
        for choice in choices:
            menu.add_radiobutton(label=choice, value=choice, variable=self.model_var,
                                 command=self._on_model_changed)
        tip = getattr(self, "_model_tip", None)
        text = (f"Whisper model: {self.model_var.get()}\n'auto' picks the largest that fits in free RAM;\n"
                "larger = more accurate but slower (downloaded on first use)")
        if tip is None:
            self._model_tip = _Tooltip(self.model_btn, text)
        else:
            tip.text = text

    def _on_model_changed(self, event=None):
        value = self.model_var.get()
        set_preference("whisper_model", "auto" if value.startswith("auto") else value)
        if value.startswith("auto"):
            self._refresh_model_combo()  # re-evaluate free RAM

    def _selected_model(self):
        value = self.model_var.get()
        return None if value.startswith("auto") else value

    def transcribe_selected(self):
        mark = self.mark_by_id(self.selected_mark_id())
        if mark is None or mark["type"] != "range" or mark.get("end") is None:
            if self.audio_duration and messagebox.askyesno(
                    "Transcribe",
                    "No range is selected.\n\nTranscribe the whole audio into a new \u201cTranscript\u201d "
                    "track, one card per sung phrase (using Whisper's own timing)?"):
                self.transcribe_whole()
            return
        self.transcribe_mark(mark["id"])

    TRANSCRIPT_TRACK_NAME = "Transcript"

    def transcribe_whole(self):
        """Transcribe all of the audio; each Whisper phrase becomes a range
        in a new "Transcript" track."""
        if self._analysis_busy or self.audio_duration is None:
            return
        if not aa.whisper_backends():
            self.transcribe_mark(None)       # shows the "install a backend" message
            return
        if not aa.stems_are_fresh(self.filepath) and aa.demucs_available() and not self.regions:
            self.append_info("\n{yellow}Separating stems before transcribing...\n")
            self.run_stem_analysis(force=False, then=lambda: self._transcribe_now(None, whole=True))
            return
        self._transcribe_now(None, whole=True)

    def transcribe_mark(self, mark_id):
        mark = self.mark_by_id(mark_id)
        if not aa.whisper_backends():
            messagebox.showinfo(
                "Transcribe",
                "Transcription needs faster-whisper, which isn't installed.\n\n"
                "Use the \u26a0 Install button in the upper right corner.")
            return
        if mark is None or self._analysis_busy:
            return
        if mark.get("label") and not messagebox.askyesno(
                "Transcribe", f"Replace the current text?\n\n\u201c{mark['label']}\u201d"):
            return
        # Use the vocal stem if it exists (or can be made) -- do that first.
        if not aa.stems_are_fresh(self.filepath) and aa.demucs_available() and not self.regions:
            self.append_info("\n{yellow}Separating stems before transcribing...\n")
            self.run_stem_analysis(force=False, then=lambda: self._transcribe_now(mark_id))
            return
        self._transcribe_now(mark_id)

    def _transcribe_now(self, mark_id, whole=False):
        mark = self.mark_by_id(mark_id)
        if (mark is None and not whole) or self._analysis_busy:
            return
        start, end = (0.0, self.audio_duration) if whole else (mark["start"], mark["end"])
        model = self._selected_model()
        regions = list(self.regions)
        self._set_analysis_busy("transcribe")
        self.append_info(f"\n{{yellow}}Transcribing {th.format_time_ms(start)} - {th.format_time_ms(end)} "
                         f"(model: {model or 'auto'})...\n")

        def work(progress):
            return aa.transcribe_range(self.filepath, start, end, model_size=model,
                                       regions=regions, progress_cb=progress)

        def done(value, error, elapsed):
            self._set_analysis_busy(None)
            if error is not None:
                self.analysis_status_var.set("Transcription failed")
                self.append_info(f"{{red}}Transcription error: " + _explained(error, "Transcription") + "\n")
                debug(1, f"{{red}}waveform_tab transcribe failed: {error}")
                self._show_text_panel()
                return
            target = self.mark_by_id(mark_id)
            text = value.get("text", "")
            if not text:
                self.analysis_status_var.set("No vocals found in range")
                self.append_info("{yellow}No vocals/words found in that range.\n")
                self._show_text_panel()
                return
            detail = (f"{value.get('backend')} {value.get('model')}, {value.get('source')}, "
                      f"{value.get('seconds_voiced', 0):.1f}s voiced, {elapsed:.1f}s")
            self.append_info(f"{{green}}Transcribed ({detail}):\n{{cyan}}  {text}\n")
            self.analysis_status_var.set("Transcribed")
            if whole:
                segments = value.get("segments") or [(start, end, text)]
                track = self._new_track(self.TRANSCRIPT_TRACK_NAME, record_history=False)
                for a, b, words in segments:
                    a, b = max(0.0, a), min(self.audio_duration, b)
                    if b - a >= th.MIN_RANGE:
                        self._add_mark("range", a, b, label=words, track_id=track["id"], source="whisper",
                                       record_history=False)
                self._mark_changed()
                self.selected = ("track", track["id"])
                self.render_waveform()
                return
            if target is None:
                self.append_info("{yellow}(the range was deleted meanwhile -- text not applied)\n")
                return
            target["label"] = text
            self._mark_changed()
            self.render_waveform()

        self._run_in_thread(work, done)

    # ------------------------------------------------------------------ export
    _EXPORT_FILETYPES = [
        ("xLights Timing", "*.xtiming"),
        ("LRC Lyrics", "*.lrc"),
        ("Audacity Labels", "*.txt"),
        ("All Files", "*.*"),
    ]

    def export_timing(self):
        """Export every track -- plus, as a track named "untitled", any
        marks still in the work area -- to one timing file, in xLights,
        LRC, or Audacity label format depending on what's chosen in the
        save dialog."""
        tracks_with_marks = []
        for tr in self.tracks:
            marks = [m for m in self.marks if m.get("track_id") == tr["id"]]
            if marks:
                tracks_with_marks.append((tr["name"], marks))
        untracked = [m for m in self.marks if m.get("track_id") is None]
        if untracked:
            tracks_with_marks.append(("untitled", untracked))
        if not tracks_with_marks:
            messagebox.showinfo("Export Timing", "There are no timing marks to export.")
            return
        initial = Path(self.filepath).stem + ".xtiming"
        path = self.ask_export_path("Export Timing", initial)
        if not path:
            return
        try:
            th.export_timing_tracks(path, tracks_with_marks)
            debug(1, f"{{green}}Exported {len(tracks_with_marks)} timing track(s) to {path}")
        except Exception as e:
            messagebox.showerror("Export Timing", f"Could not export timing:\n{e}")
            self.announce(f"Export failed: {e}")
            return
        self._exported(len(tracks_with_marks), path)

    def ask_export_path(self, title, initialfile, parent=None):
        """The Save dialog for exports: it opens in the audio file's folder
        and asks before replacing an existing file."""
        folder = str(Path(self.filepath).resolve().parent) if self.filepath else None
        kwargs = dict(title=title, initialfile=initialfile, defaultextension=".xtiming",
                      filetypes=self._EXPORT_FILETYPES, confirmoverwrite=True)
        if folder:
            kwargs["initialdir"] = folder
        if parent is not None:
            kwargs["parent"] = parent
        return filedialog.asksaveasfilename(**kwargs)

    def announce(self, message):
        """A message on the app's status bar (and the audio toolbar)."""
        self.play_status_var.set(message)
        try:
            app = self.canvas.winfo_toplevel()
            if callable(getattr(app, "set_status", None)):
                app.set_status(message)
        except (tk.TclError, AttributeError):
            pass

    def _exported(self, n_tracks, path):
        self.announce(f"Exported {n_tracks} timing track{'s' if n_tracks != 1 else ''} to {Path(path).name} "
                      f"(in {Path(path).parent})")

    def export_timing_track(self, track):
        marks = [m for m in self.marks if m.get("track_id") == track["id"]]
        if not marks:
            messagebox.showinfo("Export Timing", f"Track \"{track['name']}\" has no timing marks to export.")
            return False
        path = self.ask_export_path("Export Timing", f"{track['name']}.xtiming")
        if not path:
            return False
        try:
            th.export_timing_tracks(path, [(track["name"], marks)])
            debug(1, f"{{green}}Exported timing track '{track['name']}' to {path}")
        except Exception as e:
            messagebox.showerror("Export Timing", f"Could not export timing:\n{e}")
            self.announce(f"Export failed: {e}")
            return False
        self._exported(1, path)
        return True

    # ------------------------------------------------------------------ playback
    def _run_engine_from(self, t):
        """Start the engine at t for the rest of the current segment."""
        self._play_speed = self._play_speed_value()
        duration = None
        if self._play_seg_end is not None:
            duration = max(0.0, self._play_seg_end - t)
            if duration <= 0:
                return False
        if not self.engine.play_segment(t, duration, self._play_speed):
            self._refresh_playback_availability()
            if not th.PLAYBACK_MISSING:
                self.play_status_var.set("Playback failed to start")
            return False
        self._play_state = "playing"
        self._play_position = t
        self._play_started_wall = time.monotonic()
        return True

    def _halt_engine(self):
        self.engine.stop()
        self._play_started_wall = None

    def _restart_here(self):
        """Re-start the engine at the current position (speed/volume change)."""
        if self._play_state != "playing":
            return
        pos = self.current_play_position()
        self._halt_engine()
        self.cursor_time = pos
        self._run_engine_from(pos)

    def _play_speed_value(self):
        return {"0.5x": 0.5, "1x": 1.0, "2x": 2.0}.get(self.play_speed_var.get(), 1.0)

    def _elapsed_play_time(self):
        if self._play_started_wall is None:
            return 0.0
        return (time.monotonic() - self._play_started_wall) * self._play_speed

    def _on_play_btn_release(self, event):
        self._shift_on_play = bool(event.state & SHIFT_MASK)
        self._ctrl_on_play = bool(event.state & CONTROL_MASK)

    def _set_play_cursor(self, shift):
        try:
            self.play_btn.configure(cursor="exchange" if shift else "hand2")
        except tk.TclError:
            pass

    def _bind_shift_keys(self):
        """Update the Play button's loop cursor when Shift is pressed or
        released while the pointer is already over it (no Motion event
        then). Bound on the toplevel with add="+" so trackED's own
        bindings are kept; handlers for closed tabs just no-op."""
        def handler(event, down):
            try:
                if not self.play_btn.winfo_exists():
                    return
                x, y = self.play_btn.winfo_pointerxy()
                under = self.play_btn.winfo_containing(x, y)
                if under is self.play_btn:
                    self._set_play_cursor(down)
                elif under is not None and getattr(under, "_loop_hover", False):
                    # a timing card's Play button (timing_panel marks them)
                    under.configure(cursor="exchange" if down else "hand2")
            except (tk.TclError, KeyError):
                pass
        try:
            top = self.canvas.winfo_toplevel()
            for key in ("Shift_L", "Shift_R"):
                top.bind(f"<KeyPress-{key}>", lambda e: handler(e, True), add="+")
                top.bind(f"<KeyRelease-{key}>", lambda e: handler(e, False), add="+")
        except tk.TclError:
            pass

    def toggle_play(self):
        """Main Play/Pause button.
          stopped: play from the @cursor
          playing: pause
          paused:  start again from the starting point (where Play started,
                   or the @cursor if it was moved while paused);
                   Ctrl+click resumes from the paused spot instead
          Shift+click: (re)start as a loop."""
        loop = self._shift_on_play
        resume = getattr(self, "_ctrl_on_play", False)
        self._shift_on_play = self._ctrl_on_play = False
        if loop:
            if self._play_state == "playing":
                self._halt_engine()
                self._play_state = "stopped"
            self.start_play(loop=True)
        elif self._play_state == "playing":
            self.pause_play()
        elif self._play_state == "paused":
            if resume:
                self.start_play(loop=None)
            else:
                self.replay_from_start()
        else:
            self.start_play(loop=False)

    def cursor_moved_while_paused(self):
        paused_at = getattr(self, "_paused_at", None)
        return paused_at is not None and abs(self.cursor_time - paused_at) > 1e-6

    def replay_from_start(self):
        """Paused + Play: play again from the starting point -- the same
        loop or card span, from its start -- or, if the @cursor was moved
        while paused, plainly from there."""
        if self._play_state != "paused":
            return self.start_play(loop=False)
        moved = self.cursor_moved_while_paused()
        loop, mark_id, seg_end = self._loop, self._play_mark_id, self._play_seg_end
        self._play_state = "stopped"
        self._paused_at = None
        if moved:
            self._play_mark_id = None
            return self.start_play(loop=False)
        self.cursor_time = self._play_origin
        if loop or mark_id is not None:
            return self.start_play(loop=loop, segment=(self._play_origin, seg_end), mark_id=mark_id)
        return self.start_play(loop=False)

    def loop_segment(self):
        """Shift+Play: loop from the @cursor to the end of the selected range
        if the cursor is inside it; else loop the selected mark from its
        start (to its end, or the end of the audio for a point); with
        nothing selected, from the @cursor to the end of the audio."""
        mark = self.mark_by_id(self.selected_mark_id())
        cur = self.cursor_time
        if mark is not None:
            is_range = mark["type"] == "range" and mark.get("end") is not None
            if is_range and mark["start"] <= cur < mark["end"] - 0.01:
                return cur, mark["end"]
            return mark["start"], (mark["end"] if is_range else None)
        if self.audio_duration and cur >= self.audio_duration - 0.05:
            cur = 0.0
        return cur, None

    def start_play(self, loop=None, segment=None, mark_id=None):
        """Start (or resume) playback from the @cursor.

        - From stopped: plays [cursor, end of audio] -- or, with loop=True,
          loop_segment(); or an explicit `segment` (a card's mark). The
          position Play started from is remembered (paused + Play returns there).
        - From paused (loop=None): resumes from the @cursor (which the skip
          buttons / Ctrl+click may have moved while paused)."""
        if self.audio_duration is None or not self.filepath or self._play_state == "playing":
            return
        resuming = self._play_state == "paused" and loop is None and segment is None
        if not resuming:
            self._loop = bool(loop)
            self._play_mark_id = mark_id
            if segment is not None:
                seg_start, seg_end = segment
            elif self._loop:
                seg_start, seg_end = self.loop_segment()
            else:
                seg_start = self.cursor_time
                if seg_start >= self.audio_duration - 0.05:
                    seg_start = 0.0          # at the very end: play from the top
                seg_end = None
            self._play_seg_start, self._play_seg_end = seg_start, seg_end
            self.cursor_time = seg_start
            self._play_origin = seg_start    # paused + Play returns here
        else:
            # The cursor may have been moved while paused.
            t = self.cursor_time
            seg_end = self._play_seg_end if self._play_seg_end is not None else self.audio_duration
            if self._loop:
                t = max(self._play_seg_start, min(seg_end, t))
            elif self._play_seg_end is not None and t >= self._play_seg_end - 0.01:
                self._play_seg_end = None    # moved past the segment: play on to the end
            self.cursor_time = t
        if not self._run_engine_from(self.cursor_time):
            return
        self._update_play_controls()
        self._poll_playback()

    def pause_play(self):
        """Freeze the @cursor where playback is now."""
        if self._play_state != "playing":
            return
        pos = self.current_play_position()
        self._halt_engine()
        self.cursor_time = pos
        self._paused_at = pos
        self._play_state = "paused"
        self._update_play_controls()
        self.render_waveform()

    def stop_play(self):
        """Reset: stop, and put the @cursor back where Play started."""
        if self._play_state != "stopped":
            self._halt_engine()
            self.cursor_time = self._play_origin
        self._play_state = "stopped"
        self._loop = False
        self._play_mark_id = None
        self._update_play_highlight(None)
        self._update_play_controls()
        self.render_waveform()

    def region_boundary(self, t, direction):
        """Start (direction -1) or end (+1) of the stem region containing t;
        if t is already on that boundary, the next one out. None without
        stem regions."""
        if not self.regions:
            return None
        bounds = sorted({r["start"] for r in self.regions} | {r["end"] for r in self.regions})
        if direction < 0:
            before = [b for b in bounds if b < t - 1e-6]
            return before[-1] if before else 0.0
        after = [b for b in bounds if b > t + 1e-6]
        return after[0] if after else (self.audio_duration or t)

    def seek_to(self, t):
        """Move the @cursor to t. While playing, playback continues from
        there (a loop keeps its bounds); paused/stopped just move it."""
        if self.audio_duration is None:
            return
        t = max(0.0, min(self.audio_duration, t))
        if self._play_state == "playing":
            self._halt_engine()
            if self._loop:
                seg_end = self._play_seg_end if self._play_seg_end is not None else self.audio_duration
                t = max(self._play_seg_start, min(seg_end, t))
            elif self._play_seg_end is not None and t >= self._play_seg_end - 0.01:
                self._play_seg_end = None
            self.cursor_time = t
            self._run_engine_from(t)
            self._update_play_controls()
        else:
            self.cursor_time = t
            self._follow_playhead(t)
        self.render_waveform()

    def skip_play(self, delta):
        """◀◀ / ▶▶: move the @cursor by delta seconds (within the audio);
        with Shift, to the start/end of the stem region it's in (the audio
        start/end without stems); with Ctrl, to the start/end of the audio."""
        if self.audio_duration is None:
            return
        mods = getattr(self, "_skip_mods", 0) or 0
        self._skip_mods = 0
        here = self.cursor_position() or 0.0
        direction = -1 if delta < 0 else 1
        if mods & CONTROL_MASK:
            target = 0.0 if direction < 0 else self.audio_duration
        elif mods & SHIFT_MASK:
            target = self.region_boundary(here, direction)
            if target is None:
                target = 0.0 if direction < 0 else self.audio_duration
        else:
            target = here + delta
        self.seek_to(target)

    def current_play_position(self):
        """The moving playback position while playing, else None (when not
        playing, the position is simply the @cursor)."""
        if self._play_state != "playing":
            return None
        pos = self._play_position + self._elapsed_play_time()
        seg_end = self._play_seg_end if self._play_seg_end is not None else self.audio_duration
        if seg_end is not None:
            pos = min(pos, seg_end)
        return pos

    def _follow_playhead(self, pos):
        if self.audio_duration is None or pos is None:
            return False
        span = self.view_end - self.view_start
        if span <= 0:
            return False
        margin = span * 0.1
        if self.view_start <= pos <= self.view_end - margin:
            return False
        new_start = max(0.0, min(self.audio_duration - span, pos - span * 0.1))
        if abs(new_start - self.view_start) < 1e-9:
            return False
        self.view_start, self.view_end = new_start, new_start + span
        self._refresh_view_from_cache(render=False)  # caller renders
        return True

    def _poll_playback(self):
        """While playing: move the @cursor with playback; when the engine
        finishes on its own, loop again or stop (the cursor returns to
        where Play started, so Play replays it)."""
        if self._play_state != "playing":
            return
        if not self.engine.is_active():
            if self._loop:
                start = self._play_seg_start
                if self._run_engine_from(start):
                    self.cursor_time = start
                    self.show_time(start)
                    self.canvas.after(50, self._poll_playback)
                    return
            was_card = self._play_mark_id is not None
            self._play_started_wall = None
            self._play_state = "stopped"
            self._loop = False
            self.cursor_time = self._play_origin
            if was_card:
                self.show_time(self._play_origin)      # back at the card's start: bring it into view
            self._play_mark_id = None
            self._update_play_highlight(None)
            self._update_play_controls()
            self.render_waveform()
            return
        pos = self.current_play_position()
        self.cursor_time = pos
        self._update_play_controls()
        self._follow_playhead(pos)
        self._update_play_highlight(pos)
        self.render_waveform()
        # Poll faster near the end of a looped segment so the gap between
        # repeats stays short.
        interval = 100
        if self._loop:
            seg_end = self._play_seg_end if self._play_seg_end is not None else self.audio_duration
            if seg_end is not None and pos is not None and seg_end - pos < 0.25 * max(self._play_speed, 0.5):
                interval = 20
        self.canvas.after(interval, self._poll_playback)

    def _on_play_speed_changed(self, event=None):
        try:
            self.speed_btn.configure(text=f"{self.play_speed_var.get()} \u25be")
        except (tk.TclError, AttributeError):
            pass
        self._restart_here()

    VOLUME_STEP = 0.1
    MAX_VOLUME = 2.0

    def _saved_volume(self):
        try:
            return max(0.0, min(self.MAX_VOLUME, float(get_preference("playback_volume", 1.0))))
        except (TypeError, ValueError):
            return 1.0

    def _update_volume_label(self):
        try:
            self.vol_label.configure(text=f"vol {round(self.volume * 100):d}%")
            self.vol_down_btn.configure(state="normal" if self.volume > 1e-6 else "disabled")
            self.vol_up_btn.configure(state="normal" if self.volume < self.MAX_VOLUME - 1e-6 else "disabled")
        except (tk.TclError, AttributeError):
            pass

    def change_volume(self, delta):
        """Volume -/+ (0-200%, remembered as the "playback_volume"
        preference). Takes effect immediately, also mid-playback."""
        new = round(max(0.0, min(self.MAX_VOLUME, self.volume + delta)), 2)
        if abs(new - self.volume) < 1e-9:
            return
        self.volume = new
        self.engine.set_volume(new)
        set_preference("playback_volume", new)
        self._update_volume_label()
        self._restart_here()   # heard immediately if playing

    NAV_WIDTH = 150

    def _update_time_readout(self, force=False):
        pos = self.cursor_position() or 0.0
        total = th.format_time_ms(self.audio_duration or 0.0)
        self.time_var.set(f"{th.format_time_ms(pos):>9} / {total}")
        try:
            if force or self.pos_entry.focus_get() is not self.pos_entry:   # don't fight the user's typing
                text = th.format_time_ms(pos)
                if self.pos_entry.get() != text:
                    self.pos_entry.delete(0, "end")
                    self.pos_entry.insert(0, text)
            self.total_label.configure(text=f"/ {total}")
        except (tk.TclError, KeyError, AttributeError):
            pass
        self.view_var.set(f"{th.format_time_ms(self.view_start)} \u2013 {th.format_time_ms(self.view_end)}")
        self._draw_nav()

    def _on_pos_entered(self, event=None):
        t = th.parse_time(self.pos_entry.get())
        if t is None or self.audio_duration is None:
            self.canvas.bell()
            self._update_time_readout(force=True)
            return "break"
        self.seek_to(t)          # clamps to the audio; seeks if playing
        self.canvas.focus_set()
        self._update_time_readout(force=True)
        return "break"

    def _nav_geometry(self):
        try:
            w = max(20, int(self.nav.winfo_width()))
        except (tk.TclError, TypeError, ValueError):
            w = self.NAV_WIDTH
        if w <= 20:
            w = self.NAV_WIDTH
        total = max(self.audio_duration or 0.0, self.view_end, 1e-9)
        x0 = w * self.view_start / total
        x1 = max(x0 + 6, w * min(self.view_end, total) / total)
        return w, x0, min(w, x1)

    def _draw_nav(self):
        if self.audio_duration is None or not hasattr(self, "nav"):
            return
        c = self.nav
        try:
            c.delete("all")
            w, x0, x1 = self._nav_geometry()
            c.create_rectangle(0, 3, w, 9, fill="#3a3a3d", outline="", tags=("nav_track",))
            c.create_rectangle(x0, 1, x1, 11, fill="#8a8a90", outline="", tags=("nav_thumb",))
            pos = self.cursor_position() or 0.0
            total = max(self.audio_duration, self.view_end)
            xc = w * pos / total if total else 0
            c.create_line(xc, 0, xc, 12, fill=CURSOR_COLOR, tags=("nav_cursor",))
        except tk.TclError:
            pass

    def _on_nav_press(self, event):
        w, x0, x1 = self._nav_geometry()
        if x0 <= event.x <= x1:
            self._nav_grab = event.x - x0          # drag the thumb from where it was grabbed
        else:
            self._nav_grab = (x1 - x0) / 2         # click beside it: center the view there
            self._nav_scroll_to(event.x - self._nav_grab)
        return "break"

    def _on_nav_drag(self, event):
        self._nav_scroll_to(event.x - getattr(self, "_nav_grab", 0))
        return "break"

    def _nav_scroll_to(self, thumb_x):
        if self.audio_duration is None:
            return
        w, _x0, _x1 = self._nav_geometry()
        span = self.view_end - self.view_start
        total = max(self.audio_duration, self.view_end)
        start = max(0.0, min(max(0.0, self.audio_duration - span), thumb_x / w * total))
        if abs(start - self.view_start) < 1e-9:
            return
        self.view_start, self.view_end = start, start + span
        self._refresh_view_from_cache()

    def _update_play_controls(self):
        # U+275A heavy bars: available in far more fonts than U+23F8.
        # Plain color like the other buttons (amber while Shift is held, the
        # loop color while looping).
        normal = TB_LOOP if self._loop else TB_FG
        self.play_btn._mod_normal_fg = normal
        fg = MOD_HINT_COLORS["shift"] if "shift" in current_modifiers() else normal
        self.play_btn.configure(text="\u275a\u275a" if self._play_state == "playing" else "\u25b6",
                                fg=fg, activeforeground=fg)
        if self._play_state == "stopped":
            if not th.PLAYBACK_MISSING:
                self.play_status_var.set("")
            return
        pos = self._play_position + (self._elapsed_play_time() if self._play_state == "playing" else 0.0)
        seg_end = self._play_seg_end if self._play_seg_end is not None else self.audio_duration
        label = "Playing" if self._play_state == "playing" else "Paused"
        if self._loop:
            label = "Looping" if self._play_state == "playing" else "Paused (loop)"
        self.play_status_var.set(f"{label} \u00b7 segment ends {th.format_time_ms(seg_end)}")

    def stop_and_release(self):
        """Called when the tab/file is going away -- stop playback and
        release the engine's resources."""
        self.engine.stop()
        self.engine.close()

    # ------------------------------------------------------------------ hit-testing
    def _time_at_x(self, x):
        w = self._canvas_size()[0]
        frac = max(0.0, min(1.0, x / w))
        t = self.view_start + frac * (self.view_end - self.view_start)
        if self.audio_duration is not None:
            t = min(t, self.audio_duration)  # the view may extend past the end; marks can't
        return t

    def _track_layout(self):
        """Canvas rows, top to bottom: waveform (work area), the combined
        status / new-track drop row, then the named track bands."""
        total_h = self._canvas_size()[1]
        reserved = self.STATUS_ROW_HEIGHT + len(self.tracks) * self.TRACK_HEIGHT
        work_height = max(60, total_h - reserved)
        return {"total_h": total_h, "work_height": work_height,
                "row_top": work_height, "track_top": work_height + self.STATUS_ROW_HEIGHT}

    def _track_zone_at_y(self, y):
        layout = self._track_layout()
        if y < layout["work_height"]:
            return "work", None
        if y < layout["track_top"]:
            return "new_track", None          # the status row doubles as the drop target
        idx = int((y - layout["track_top"]) // self.TRACK_HEIGHT)
        if 0 <= idx < len(self.tracks):
            return "track", self.tracks[idx]["id"]
        return "new_track", None

    def _is_highlighted(self, kind, item_id):
        target = (kind, item_id)
        if self.selected == target or self._hover == target:
            return True
        return kind == "mark" and len(getattr(self, "_multi", ())) > 1 and item_id in self.selected_mark_ids()

    def _track_label_hit(self, track_id, x, y):
        bbox = self._track_label_regions.get(track_id)
        if not bbox:
            return False
        x1, y1, x2, y2 = bbox
        return x1 - 4 <= x <= x2 + 4 and y1 - 4 <= y <= y2 + 4

    def _mark_and_edge_at_x(self, x, pool=None):
        if pool is None:
            pool = [m for m in self.marks if m.get("track_id") is None]
        w = self._canvas_size()[0]
        span = self.view_end - self.view_start
        if span <= 0:
            return None, None
        x_of = lambda t: (t - self.view_start) / span * w
        tolerance = self.EDGE_ZONE
        for m in pool:
            if m["type"] == "point":
                if not (self.view_start <= m["start"] <= self.view_end):
                    continue
                if abs(x - x_of(m["start"])) <= tolerance:
                    return m, None
            else:
                if m["end"] < self.view_start or m["start"] > self.view_end:
                    continue
                x1 = x_of(max(m["start"], self.view_start))
                x2 = x_of(min(m["end"], self.view_end))
                if x1 - tolerance <= x <= x2 + tolerance:
                    if abs(x - x1) <= self.EDGE_ZONE and abs(x - x1) <= abs(x - x2):
                        return m, "start"
                    if abs(x - x2) <= self.EDGE_ZONE:
                        return m, "end"
                    return m, None
        return None, None

    def _cursor_for_edge(self, edge):
        if edge == "start":
            return "left_side"
        if edge == "end":
            return "right_side"
        # Whole-mark move: 4-way arrow, since a mark can also be dragged
        # vertically (into/out of/between track bands).
        return "fleur"

    def _selected_work_mark_at(self, x, y):
        if not self.selected or self.selected[0] != "mark":
            return None
        mark = next((m for m in self.marks if m["id"] == self.selected[1]), None)
        if mark is None or mark.get("track_id") is not None:
            return None
        if self.audio_duration is None or self.view_end <= self.view_start:
            return None
        layout = self._track_layout()
        if not (0 <= y < layout["work_height"]):
            return None
        w = self._canvas_size()[0]
        span = self.view_end - self.view_start
        x_of = lambda t: (t - self.view_start) / span * w
        if mark["type"] == "range":
            x1, x2 = x_of(mark["start"]), x_of(mark["end"])
            if min(x1, x2) - self.EDGE_ZONE <= x <= max(x1, x2) + self.EDGE_ZONE:
                return mark
        else:
            if abs(x - x_of(mark["start"])) <= self.EDGE_ZONE:
                return mark
        return None

    # ------------------------------------------------------------------ mouse/keyboard
    def _on_waveform_motion(self, event):
        if self._move_drag or self._press_info or self._track_drag:
            return
        if self._legend_kind_at(event.x, event.y) is not None:
            self.canvas.configure(cursor="hand2")
            return
        cursor = ""
        hit = None
        if self.audio_duration is not None and self.view_end > self.view_start:
            zone, target = self._track_zone_at_y(event.y)
            if zone == "work":
                if event.y >= self.LABEL_ZONE_HEIGHT:
                    mark, edge = self._mark_and_edge_at_x(event.x)
                    if mark is not None:
                        cursor = self._cursor_for_edge(edge)
                        hit = ("mark", mark["id"])
            elif zone == "track":
                if self._track_label_hit(target, event.x, event.y):
                    cursor = "fleur"
                    hit = ("track", target)
                else:
                    pool = [m for m in self.marks if m.get("track_id") == target]
                    mark, edge = self._mark_and_edge_at_x(event.x, pool=pool)
                    if mark is not None:
                        cursor = self._cursor_for_edge(edge)
                        hit = ("mark", mark["id"])
        self.canvas.configure(cursor=cursor)
        if hit != self._hover:
            self._hover = hit
            self.render_waveform()

    def _on_waveform_leave(self, event):
        if self._hover is not None:
            self._hover = None
            self.render_waveform()

    def _deselect(self):
        if self.selected is not None:
            self.selected = None
            self.render_waveform()

    def _on_waveform_press(self, event):
        crumb(f"waveform press y={event.y}")
        if self.audio_duration is None or self.view_end <= self.view_start:
            return
        self._move_drag = None
        self._press_info = None
        self._track_drag = None
        kind = self._legend_kind_at(event.x, event.y)
        if kind is not None:           # the stem color key: pick a new color
            self.pick_stem_color(kind)
            return

        zone, target = self._track_zone_at_y(event.y)

        if zone == "track":
            if self._track_label_hit(target, event.x, event.y):
                self.selected = ("track", target)
                self._track_drag = {"track_id": target}
                self.canvas.configure(cursor="fleur")
                self.render_waveform()
                return
            pool = [m for m in self.marks if m.get("track_id") == target]
            hit_mark, edge = self._mark_and_edge_at_x(event.x, pool=pool)
            if hit_mark is not None and event.state & SHIFT_MASK:
                self.extend_selection(hit_mark, toggle=False)      # Shift+click: a run of marks
                return
            if hit_mark is not None:
                self._start_move_drag(hit_mark, edge, event)
                return
            self._multi = []
            self._deselect()
            return

        if zone == "new_track":
            # like a click on the waveform: just move the @cursor (a
            # selected track stays selected)
            self.seek_to(self._time_at_x(event.x))
            return

        if event.y >= self.LABEL_ZONE_HEIGHT:
            hit_mark, edge = self._mark_and_edge_at_x(event.x)
            if hit_mark is not None:
                self._start_move_drag(hit_mark, edge, event)
                return
        self._press_info = {
            "x": event.x, "time": self._time_at_x(event.x),
            "shift": bool(event.state & 0x0001), "dragging": False,
        }

    def _start_move_drag(self, hit_mark, edge, event):
        """Press on a mark: select it and get ready to drag it. When it's
        one of several selected marks and the press is on its body (not an
        edge), the whole selection moves together -- in time, and onto
        another track / the waveform. An edge resizes just that mark."""
        group_ids = self.selected_mark_ids()
        in_group = len(group_ids) > 1 and hit_mark["id"] in group_ids
        if not in_group:
            self._multi = []
        self.selected = ("mark", hit_mark["id"])
        group = []
        if in_group and edge is None:
            group = [(m, m["start"], m.get("end")) for m in self._selected_marks(group_ids)]
        self._move_drag = {
            "mark": hit_mark, "edge": edge,
            "start_orig": hit_mark["start"], "end_orig": hit_mark.get("end"),
            "press_time": self._time_at_x(event.x), "orig_track_id": hit_mark.get("track_id"),
            "group": group,
        }
        self.canvas.configure(cursor=self._cursor_for_edge(edge))
        self.render_waveform()

    def _drag_group(self, event, crossing_rows):
        """Move every selected mark by the same (snapped) time, keeping the
        whole block inside 0 .. the end; crossing rows puts them back at
        their own times (the drop decides the track)."""
        group = self._move_drag["group"]
        if crossing_rows:
            delta = 0.0
        else:
            delta = self._snap_delta(self._time_at_x(event.x) - self._move_drag["press_time"], event)
            first = min(s0 for _m, s0, _e0 in group)
            last = max((e0 if e0 is not None else s0) for _m, s0, e0 in group)
            delta = max(-first, min(self.max_mark_time() - last, delta))
        for m, s0, e0 in group:
            m["start"] = s0 + delta
            if e0 is not None:
                m["end"] = e0 + delta

    def _on_waveform_drag(self, event):
        if self._track_drag:
            self._drag_reorder_track(event)
            return
        if self._move_drag:
            self._drag_move_mark(event)
            return
        if not self._press_info or self.audio_duration is None:
            return
        if not self._press_info["dragging"] and abs(event.x - self._press_info["x"]) < 4:
            return
        self._press_info["dragging"] = True
        current_time = self._snap_time(self._time_at_x(event.x), event)
        anchor = self._snap_time(self._press_info["time"], event)
        self._preview_range = (min(anchor, current_time), max(anchor, current_time))
        self._press_info["last_xy"] = (event.x, event.y)
        self.render_waveform()

    def _snap_time(self, t, event):
        if event.state & 0x0001:
            return t
        interval = th.time_grid_interval(self.view_end - self.view_start)
        return round(t / interval) * interval if interval > 0 else t

    def _snap_delta(self, delta, event):
        """Moving/resizing a mark by dragging: snap to a fine "nice" step
        (about 1/200 of the view -- the grid lines' spacing made the mark
        stay put until the pointer had moved half a grid square); Shift:
        no snapping."""
        if event.state & 0x0001:
            return delta
        interval = th.time_grid_interval(self.view_end - self.view_start, target_lines=self.DRAG_SNAP_STEPS)
        if interval <= 0:
            return delta
        return round(delta / interval) * interval

    def _drag_reorder_track(self, event):
        track_id = self._track_drag["track_id"]
        cur_idx = next((i for i, t in enumerate(self.tracks) if t["id"] == track_id), None)
        if cur_idx is None:
            return
        layout = self._track_layout()
        idx = int((event.y - layout["track_top"]) // self.TRACK_HEIGHT)
        idx = max(0, min(len(self.tracks) - 1, idx))
        if idx != cur_idx:
            track = self.tracks.pop(cur_idx)
            self.tracks.insert(idx, track)
            self._mark_changed()
            self.render_waveform()

    def _drag_move_mark(self, event):
        duration = self.audio_duration or 0.0
        mark = self._move_drag["mark"]
        edge = self._move_drag.get("edge")
        min_span = 0.01

        orig_track_id = self._move_drag.get("orig_track_id")
        orig_zone = ("work", None) if orig_track_id is None else ("track", orig_track_id)
        current_zone = self._track_zone_at_y(event.y)
        crossing_rows = edge is None and current_zone != orig_zone

        if self._move_drag.get("group"):
            self._drag_group(event, crossing_rows)
            self.canvas.configure(cursor="hand2" if crossing_rows else self._cursor_for_edge(edge))
        elif crossing_rows:
            mark["start"] = self._move_drag["start_orig"]
            if mark["type"] == "range":
                mark["end"] = self._move_drag["end_orig"]
            self.canvas.configure(cursor="hand2")
        else:
            current_time = self._time_at_x(event.x)
            delta = self._snap_delta(current_time - self._move_drag["press_time"], event)
            if mark["type"] == "point" or edge is None:
                if mark["type"] == "point":
                    mark["start"] = max(0.0, min(duration, self._move_drag["start_orig"] + delta))
                else:
                    span = self._move_drag["end_orig"] - self._move_drag["start_orig"]
                    new_start = self._move_drag["start_orig"] + delta
                    new_start = max(0.0, min(self.max_mark_time() - span, new_start))
                    mark["start"] = new_start
                    mark["end"] = new_start + span
            elif edge == "start":
                new_start = self._move_drag["start_orig"] + delta
                new_start = max(0.0, min(self._move_drag["end_orig"] - min_span, new_start))
                mark["start"] = new_start
            else:
                new_end = self._move_drag["end_orig"] + delta
                new_end = min(self.max_mark_time(), max(self._move_drag["start_orig"] + min_span, new_end))
                mark["end"] = new_end
            self.canvas.configure(cursor=self._cursor_for_edge(edge))
        if edge is None:
            self._move_drag["preview_zone"] = current_zone
        self._move_drag["moved"] = True
        self._move_drag["last_xy"] = (event.x, event.y)
        self.render_waveform()

    def _on_waveform_release(self, event):
        if self._track_drag:
            self._track_drag = None
            self.render_waveform()
            self._on_waveform_motion(event)
            return
        if self._move_drag:
            mark = self._move_drag["mark"]
            edge = self._move_drag.get("edge")
            moving = [m for m, _s, _e in self._move_drag.get("group") or []] or [mark]
            if self._move_drag.get("group") and not self._move_drag.get("moved"):
                self._multi = []         # a plain click on one of several selected marks selects just it
            if edge is None:
                zone, target = self._track_zone_at_y(event.y)
                if zone == "work":
                    for m in moving:
                        m["track_id"] = None
                elif zone == "track":
                    for m in moving:
                        m["track_id"] = target
                else:
                    self._prompt_new_track_for_marks(moving)
            self._move_drag = None
            self._mark_changed()
            self.render_waveform()
            self._on_waveform_motion(event)
            return
        if not self._press_info:
            return
        new_mark = None
        prompt_for_label = True
        if self._press_info["dragging"] and self._preview_range:
            start_t, end_t = self._preview_range
            if end_t - start_t > 0.01:
                new_mark = self._add_mark("range", start_t, end_t)
                self.selected = ("mark", new_mark["id"])
                self._last_click_mark_id = None
            self._preview_range = None
        else:
            clicked_time = self._press_info["time"]
            if self._press_info["shift"]:
                # Shift+click extends the point the previous click just made
                # into a range; with no such click, it runs from the @cursor.
                last = self.mark_by_id(self._last_click_mark_id)
                if last is not None and last["type"] == "point" and last.get("track_id") is None:
                    anchor, label = last["start"], last.get("label", "")
                    self.marks.remove(last)
                else:
                    anchor, label = self.cursor_time, ""
                lo, hi = min(anchor, clicked_time), max(anchor, clicked_time)
                if hi - lo >= th.MIN_RANGE:
                    new_mark = self._add_mark("range", lo, hi, label=label)
                else:
                    new_mark = self._add_mark("point", clicked_time, None, label=label)
                prompt_for_label = False
                self._last_click_mark_id = None
            else:
                # A plain click just moves the @cursor (seeks while playing).
                self._last_click_mark_id = None
                self._press_info = None
                self.seek_to(clicked_time)
                self._on_waveform_motion(event)
                return
            self.selected = ("mark", new_mark["id"])
        self._press_info = None
        self.render_waveform()
        self._on_waveform_motion(event)
        if new_mark is not None and prompt_for_label:
            self._edit_mark_label(new_mark)

    def _on_key_up(self, event):
        self._move_selected_vertically(-1)
        return "break"

    def _on_key_down(self, event):
        self._move_selected_vertically(1)
        return "break"

    def _move_selected_vertically(self, direction):
        if not self.selected or self.audio_duration is None:
            return
        kind, sel_id = self.selected
        if kind == "track":
            idx = next((i for i, t in enumerate(self.tracks) if t["id"] == sel_id), None)
            if idx is None:
                return
            new_idx = idx + direction
            if 0 <= new_idx < len(self.tracks):
                track = self.tracks.pop(idx)
                self.tracks.insert(new_idx, track)
                self._mark_changed()
                self.render_waveform()
            return

        mark = next((m for m in self.marks if m["id"] == sel_id), None)
        if mark is None:
            return
        track_id = mark.get("track_id")
        if track_id is None:
            if direction > 0:
                if self.tracks:
                    mark["track_id"] = self.tracks[0]["id"]
                    self._mark_changed()
                    self.render_waveform()
                else:
                    self._prompt_new_track_for_mark(mark)
            return
        idx = next((i for i, t in enumerate(self.tracks) if t["id"] == track_id), None)
        if idx is None:
            return
        new_idx = idx + direction
        if new_idx < 0:
            mark["track_id"] = None
            self._mark_changed()
            self.render_waveform()
        elif new_idx < len(self.tracks):
            mark["track_id"] = self.tracks[new_idx]["id"]
            self._mark_changed()
            self.render_waveform()
        else:
            self._prompt_new_track_for_mark(mark)

    def _on_key_left(self, event):
        self._nudge_selected_horizontally(-1)
        return "break"

    def _on_key_right(self, event):
        self._nudge_selected_horizontally(1)
        return "break"

    def _nudge_selected_horizontally(self, direction):
        if not self.selected or self.selected[0] != "mark" or self.audio_duration is None:
            return
        mark = next((m for m in self.marks if m["id"] == self.selected[1]), None)
        if mark is None:
            return
        interval = th.time_grid_interval(self.view_end - self.view_start)
        delta = direction * interval
        duration = self.audio_duration
        if mark["type"] == "point":
            mark["start"] = max(0.0, min(duration, mark["start"] + delta))
        else:
            span = mark["end"] - mark["start"]
            new_start = max(0.0, min(duration - span, mark["start"] + delta))
            mark["start"] = new_start
            mark["end"] = new_start + span
        self._mark_changed()
        self.render_waveform()

    def _on_key_delete(self, event):
        if not self.selected:
            return "break"
        kind, sel_id = self.selected
        if kind == "mark" and len(self.selected_mark_ids()) > 1:
            self.delete_selection()
        elif kind == "mark":
            mark = next((m for m in self.marks if m["id"] == sel_id), None)
            if mark is not None:
                self._delete_mark(mark)
        else:
            track = next((t for t in self.tracks if t["id"] == sel_id), None)
            if track is not None:
                self._delete_track(track)
        return "break"

    def _on_key_escape(self, event):
        self._multi = []
        if self.selected is not None:
            self.selected = None
            self.render_waveform()
        return "break"

    def _on_key_tab(self, event):
        self._select_adjacent_mark(1)
        return "break"

    def _on_key_shift_tab(self, event):
        self._select_adjacent_mark(-1)
        return "break"

    def _select_adjacent_mark(self, direction):
        if not self.marks:
            return
        ordered = sorted(self.marks, key=lambda m: (m["start"], m["id"]))
        current_idx = None
        if self.selected and self.selected[0] == "mark":
            current_idx = next((i for i, m in enumerate(ordered) if m["id"] == self.selected[1]), None)
        if current_idx is None:
            new_idx = 0 if direction > 0 else len(ordered) - 1
        else:
            new_idx = (current_idx + direction) % len(ordered)
        mark = ordered[new_idx]
        self.selected = ("mark", mark["id"])
        self._hover = None
        self._ensure_mark_visible(mark)
        self.render_waveform()

    def mark_play_position(self, mark):
        """Where the card's Play would start: the paused position if this
        mark is paused inside its span, else its start."""
        if self._play_mark_id == mark["id"] and self._play_state == "paused":
            end = mark.get("end") if mark["type"] == "range" else None
            if mark["start"] <= self.cursor_time and (end is None or self.cursor_time <= end):
                return self.cursor_time
        return mark["start"]

    def _ensure_mark_visible(self, mark):
        """Scroll (not zoom) the waveform so the card's next play position
        is visible -- and, if the whole card fits at this zoom, its end
        too. Returns True if the view moved (the caller renders)."""
        if self.audio_duration is None:
            return False
        span = self.view_end - self.view_start
        if span <= 0:
            return False
        margin = span * 0.05
        pos = self.mark_play_position(mark)
        end = mark["end"] if mark["type"] == "range" and mark.get("end") is not None else pos
        new_start = self.view_start
        if end - pos <= span - 2 * margin:            # the rest of the card fits: show pos..end
            if pos < self.view_start + (margin if self.view_start > 0 else 0):
                new_start = pos - margin
            elif end > self.view_end - margin:
                new_start = end + margin - span
        elif not (self.view_start <= pos <= self.view_end - margin):
            new_start = pos - margin
        new_start = max(0.0, min(self.audio_duration * self.OVERSHOOT_FACTOR - span, new_start))
        if abs(new_start - self.view_start) < 1e-9:
            return False
        self.view_start, self.view_end = new_start, new_start + span
        self._refresh_view_from_cache(render=False)  # caller renders
        return True

    def reveal_mark(self, mark_id):
        """A card got focus: show it in the waveform (see _ensure_mark_visible)."""
        mark = self.mark_by_id(mark_id)
        if mark is not None and self._ensure_mark_visible(mark):
            self.render_waveform()

    def _on_waveform_wheel(self, event):
        if self.audio_duration is None:
            return
        if getattr(event, "num", None) == 4:
            direction = "in"
        elif getattr(event, "num", None) == 5:
            direction = "out"
        elif getattr(event, "delta", None):
            direction = "in" if event.delta > 0 else "out"
        else:
            return
        self.zoom_waveform(direction)
        return "break"

    def add_point_at(self, t, label=""):
        """A new point mark at t (double-click on empty waveform, or M)."""
        if self.audio_duration is None:
            return None
        t = max(0.0, min(self.audio_duration, t))
        mark = self._add_mark("point", t, None, label=label)
        self._last_click_mark_id = mark["id"]     # a following Shift+click extends it
        self.selected = ("mark", mark["id"])
        self.render_waveform()
        return mark

    def _on_waveform_double_click(self, event):
        for tr in self.tracks:
            if self._track_label_hit(tr["id"], event.x, event.y):
                self._rename_track(tr)
                return "break"
        mark = self._selected_work_mark_at(event.x, event.y)
        if mark is None:
            hit_id = None
            for mark_id, bbox in self._mark_hit_regions.items():
                if not bbox:
                    continue
                x1, y1, x2, y2 = bbox
                if x1 - 4 <= event.x <= x2 + 4 and y1 - 4 <= event.y <= y2 + 4:
                    hit_id = mark_id
                    break
            if hit_id is not None:
                mark = next((m for m in self.marks if m["id"] == hit_id), None)
        if mark is not None:
            self._edit_mark_label(mark)
        elif self._track_zone_at_y(event.y)[0] == "work" and self.audio_duration is not None:
            # empty waveform: a new point mark here (the first click already moved the @cursor)
            new_mark = self.add_point_at(self._time_at_x(event.x))
            if new_mark is not None:
                self._edit_mark_label(new_mark)
        return "break"

    TEXT_IMPORT_EXTS = {".txt", ".lrc", ".lab", ".srt", ".labels"}

    def import_text_track(self, path):
        """New timing track from a text file: LRC / Audacity labels / SRT
        timestamps become one card each; plain lyrics become one card
        spanning the whole audio (use Split \u25be > Split into words)."""
        if self.audio_duration is None:
            return None
        try:
            with open(path, "r", encoding="utf-8-sig", errors="replace") as f:
                text = f.read()
        except OSError as exc:
            messagebox.showerror("Import", f"Couldn't read {path}:\n{exc}")
            return None
        fmt, items = th.parse_timed_text(text, self.audio_duration)
        track = self._new_track(Path(path).stem, record_history=False)
        count = 0
        if items:
            for a, b, label in items:
                if a >= self.audio_duration:
                    continue
                b = min(self.audio_duration, b) if b is not None else None
                kind = "range" if b is not None and b - a >= th.MIN_RANGE else "point"
                self._add_mark(kind, a, b if kind == "range" else None, label=label, track_id=track["id"],
                               source="import", record_history=False)
                count += 1
        else:
            lyrics = "\n".join(line.rstrip() for line in text.strip().splitlines())
            if lyrics:
                self._add_mark("range", 0.0, self.audio_duration, label=lyrics, track_id=track["id"],
                               source="import", record_history=False)
                count = 1
        self._mark_changed()
        self.selected = ("track", track["id"])
        self.render_waveform()
        what = {"lrc": "LRC", "audacity": "Audacity labels", "srt": "SRT", "plain": "plain text"}[fmt]
        self.append_info(f"{{green}}Imported {Path(path).name} ({what}): {count} card(s) in track "
                         f"\u201c{track['name']}\u201d\n")
        return track

    def _import_text_dialog(self):
        path = filedialog.askopenfilename(
            title="Import lyrics / labels as a timing track",
            filetypes=[("Lyrics and labels", "*.txt *.lrc *.srt *.lab *.labels"), ("All files", "*.*")])
        if path:
            self.import_text_track(path)

    def _setup_file_drop(self):
        """With tkinterdnd2 (MIT; the app's optional drag-and-drop), a text
        file dropped on the status / new-track row becomes a timing track.
        Other drops on the waveform are passed to the app (open as a tab)."""
        c = self.canvas
        try:
            from tkinterdnd2 import DND_FILES
            c.drop_target_register(DND_FILES)
        except Exception:
            return False
        c._own_drop = True                 # tracked.py doesn't re-register it
        c.dnd_bind("<<DropEnter>>", lambda e: getattr(e, "action", "copy") or "copy")
        c.dnd_bind("<<DropPosition>>", self._on_drop_position)
        c.dnd_bind("<<DropLeave>>", lambda e: self._set_drop_hover(False))
        c.dnd_bind("<<Drop>>", self._on_file_drop)
        return True

    def _drop_in_row(self, event):
        try:
            y = int(event.y_root) - self.canvas.winfo_rooty()
        except (tk.TclError, TypeError, ValueError, AttributeError):
            return False
        return self._track_zone_at_y(y)[0] == "new_track"

    def _set_drop_hover(self, on):
        if getattr(self, "_drop_hover", False) != on:
            self._drop_hover = on
            self.render_waveform()

    def _on_drop_position(self, event):
        self._set_drop_hover(self._drop_in_row(event))
        return getattr(event, "action", "copy")

    def _on_file_drop(self, event):
        self._set_drop_hover(False)
        try:
            paths = [p.strip("{}") for p in self.canvas.tk.splitlist(event.data)]
        except Exception:
            paths = [str(event.data).strip("{}")]
        if self._drop_in_row(event):
            texts = [p for p in paths if Path(p).suffix.lower() in self.TEXT_IMPORT_EXTS and Path(p).is_file()]
            for p in texts:
                self.import_text_track(p)
            if texts:
                return getattr(event, "action", "copy")
        app = self.canvas.winfo_toplevel()
        handler = getattr(app, "_on_drop", None)
        if callable(handler):
            handler(event)                 # not a lyrics drop: open it in a tab as usual
        return getattr(event, "action", "copy")

    def _on_waveform_right_click(self, event):
        for tr in self.tracks:
            if self._track_label_hit(tr["id"], event.x, event.y):
                self._show_track_menu(tr, event)
                return

        if self.audio_duration is not None and self._track_zone_at_y(event.y)[0] == "new_track":
            menu = tk.Menu(self.canvas, tearoff=False)
            menu.add_command(label="Import lyrics / labels file as a new track...", command=self._import_text_dialog)
            menu.add_command(label="(or drag a .txt / .lrc / .srt / Audacity labels file here)", state="disabled")
            try:
                menu.tk_popup(event.x_root, event.y_root)
            finally:
                menu.grab_release()
            return
        mark = self._selected_work_mark_at(event.x, event.y)
        if mark is None:
            zone, target = self._track_zone_at_y(event.y)
            if zone == "track":
                pool = [m for m in self.marks if m.get("track_id") == target]
                mark, _edge = self._mark_and_edge_at_x(event.x, pool=pool)
                if mark is None and _MARK_CLIPBOARD["marks"]:
                    menu = tk.Menu(self.canvas, tearoff=False)
                    self._add_paste_items(menu, target)
                    menu.tk_popup(event.x_root, event.y_root)
                    return
        if mark is None:
            hit_id = None
            for mark_id, bbox in self._mark_hit_regions.items():
                if not bbox:
                    continue
                x1, y1, x2, y2 = bbox
                if x1 - 4 <= event.x <= x2 + 4 and y1 - 4 <= event.y <= y2 + 4:
                    hit_id = mark_id
                    break
            if hit_id is None:
                return
            mark = next((m for m in self.marks if m["id"] == hit_id), None)
            if mark is None:
                return
        if mark["id"] not in self.selected_mark_ids():
            self._multi = []
        if self.selected != ("mark", mark["id"]):
            self.selected = ("mark", mark["id"])
            self.render_waveform()
        group = self.selected_mark_ids()
        if len(group) > 1:
            self._show_group_menu(group, event)
            return

        is_range = mark["type"] == "range" and mark.get("end") is not None
        cur = self.cursor_position()
        can_split = th.plan_split(mark, at_time=cur) is not None
        prev_m = th.neighbor_mark(self.marks, mark, -1)
        next_m = th.neighbor_mark(self.marks, mark, 1)

        menu = tk.Menu(self.canvas, tearoff=False)
        cursor_inside = is_range and cur is not None and mark["start"] < cur < mark["end"]
        menu.add_command(label="Split at Cursor" if cursor_inside else "Split at Middle",
                         state="normal" if can_split else "disabled",
                         command=lambda: self.split_mark_by_id(mark["id"]))
        menu.add_command(label="Merge with Previous", state="normal" if prev_m else "disabled",
                         command=lambda: self.merge_mark_by_id(mark["id"], -1))
        menu.add_command(label="Merge with Next", state="normal" if next_m else "disabled",
                         command=lambda: self.merge_mark_by_id(mark["id"], 1))
        menu.add_command(label="Transcribe Range", state="normal" if is_range and not self._analysis_busy
                         else "disabled", command=lambda: self.transcribe_mark(mark["id"]))
        menu.add_separator()
        voices_now = mark.get("voices") or []
        voice_menu = tk.Menu(menu, tearoff=False, bg="#ffffff", fg="#1e1e1e")
        self.fill_voice_menu(voice_menu, mark["id"])
        menu.add_cascade(label="Voices: " + (", ".join(voices_now) if voices_now else "(none)"), menu=voice_menu)
        self._last_voice_menu = voice_menu
        menu.add_separator()
        if mark["label"]:
            menu.add_command(label="Edit Label...", command=lambda: self._edit_mark_label(mark))
            menu.add_command(label="Delete Label", command=lambda: self._clear_mark_label(mark))
        else:
            menu.add_command(label="Add Label...", command=lambda: self._edit_mark_label(mark))
        if mark.get("track_id") is None:
            menu.add_command(label="Set Duration...", command=lambda: self._set_mark_duration(mark))
        track_labels = [m.get("label", "") for m in self.track_marks(mark.get("track_id"))] \
            if mark.get("track_id") else []
        n_pieces = len(mark.get("pieces") or [])
        if n_pieces >= 2:
            menu.add_command(label=f"Unmerge into {n_pieces} Cards", command=lambda: self.unmerge_mark_by_id(mark["id"]))
        if th.numbering_cycle(track_labels) is not None:
            menu.add_command(label="Renumber from Here...", command=lambda: self.renumber_from_mark(mark["id"]))
        menu.add_separator()
        self._add_shift_items(menu, [mark["id"]])
        self._add_clipboard_items(menu, [mark["id"]])
        menu.add_separator()
        menu.add_command(label="Delete Mark", command=lambda: self._delete_mark(mark))
        menu.add_command(label="Delete All Marks", command=self._delete_all_marks)
        menu.tk_popup(event.x_root, event.y_root)

    # ------------------------------------------------------------------ multi-select / clipboard
    def selected_mark_ids(self):
        """The selected marks: the Ctrl/Shift+click group (marks of one
        track) when the selected mark is in it, else just that mark."""
        sel = self.selected_mark_id()
        if sel is None:
            return []
        multi = [mid for mid in getattr(self, "_multi", []) if self.mark_by_id(mid) is not None]
        return multi if sel in multi else [sel]

    def extend_selection(self, mark, toggle):
        """toggle=True (Ctrl+click): add/remove one mark; toggle=False
        (Shift+click): every mark of the track from the selected one to
        this one. The group stays within one track."""
        track_id = mark.get("track_id")
        current = [mid for mid in self.selected_mark_ids()
                   if (self.mark_by_id(mid) or {}).get("track_id") == track_id]
        if toggle:
            ids = list(current)
            if mark["id"] in ids:
                ids.remove(mark["id"])
            else:
                ids.append(mark["id"])
            primary = mark["id"] if mark["id"] in ids else (ids[-1] if ids else None)
        else:
            anchor = self.mark_by_id(self.selected_mark_id())
            ordered = sorted(self.track_marks(track_id), key=lambda m: (m["start"], m["id"]))
            order = [m["id"] for m in ordered]
            if anchor is None or anchor.get("track_id") != track_id or anchor["id"] not in order:
                ids = [mark["id"]]
            else:
                i, j = sorted((order.index(anchor["id"]), order.index(mark["id"])))
                ids = order[i:j + 1]
            primary = mark["id"]
        self._multi = ids
        self.selected = ("mark", primary) if primary else (("track", track_id) if track_id else None)
        self.render_waveform()

    def _selected_marks(self, ids=None):
        ids = self.selected_mark_ids() if ids is None else ids
        return [m for m in (self.mark_by_id(i) for i in ids) if m is not None]

    def copy_selection(self, ids=None):
        marks = self._selected_marks(ids)
        if not marks:
            return 0
        _MARK_CLIPBOARD["marks"] = copy.deepcopy(sorted(marks, key=lambda m: m["start"]))
        n = len(marks)
        self.play_status_var.set(f"Copied {n} mark{'s' if n != 1 else ''}")
        return n

    def cut_selection(self, ids=None):
        n = self.copy_selection(ids)
        if n:
            self.delete_selection(ids)
            self.play_status_var.set(f"Cut {n} mark{'s' if n != 1 else ''}")
        return n

    def delete_selection(self, ids=None):
        """Delete the selected marks (one undo step); the track keeps the focus."""
        marks = self._selected_marks(ids)
        if not marks:
            return 0
        gone = {m["id"] for m in marks}
        track_id = marks[0].get("track_id")
        self.marks = [m for m in self.marks if m["id"] not in gone]
        self._multi = []
        self.selected = ("track", track_id) if track_id else None
        self._mark_changed()
        self.render_waveform()
        return len(gone)

    def _target_track_id(self):
        """Where Ctrl+V pastes: the selected track, or the selected mark's track."""
        if not self.selected:
            return None
        kind, sel_id = self.selected
        if kind == "track":
            return sel_id
        mark = self.mark_by_id(sel_id)
        return mark.get("track_id") if mark else None

    def _ask_track(self, track_id):
        """track_id, or "new": ask for a name and make the track (no undo step)."""
        if track_id != "new":
            return track_id
        name = simpledialog.askstring("New Timing Track", "Track name:")
        if not (name and name.strip()):
            return None
        return self._new_track(name.strip(), record_history=False)["id"]

    def paste_marks(self, track_id=None, at_cursor=False):
        """Paste the copied marks into a track (Ctrl+V: the selected
        track), at their own times -- or, at_cursor, shifted so the first
        starts at the @cursor. The pasted marks become the selection."""
        src = _MARK_CLIPBOARD["marks"]
        if not src or self.audio_duration is None:
            return []
        track_id = self._target_track_id() if track_id is None else self._ask_track(track_id)
        if track_id is None or self.track_by_id(track_id) is None:
            self.play_status_var.set("Select a track to paste into")
            return []
        offset = (self.cursor_position() or 0.0) - src[0]["start"] if at_cursor else 0.0
        limit = self.max_mark_time()
        new = [m for m in th.copy_marks(src, track_id, lambda: uuid.uuid4().hex[:8], offset)
               if 0.0 <= m["start"] <= limit]
        for m in new:
            if m.get("end") is not None:
                m["end"] = min(m["end"], limit)
            m["source"] = "user"
        if not new:
            return []
        self.marks.extend(new)
        self._multi = [m["id"] for m in new]
        self.selected = ("mark", new[0]["id"])
        self._mark_changed()
        self.render_waveform()
        self.play_status_var.set(f"Pasted {len(new)} mark{'s' if len(new) != 1 else ''}")
        return new

    def move_selection_to_track(self, track_id, ids=None, keep=False):
        """Move (keep=False) or copy (keep=True) marks to another track
        ("new": ask for a name). One undo step."""
        marks = self._selected_marks(ids)
        if not marks:
            return []
        track_id = self._ask_track(track_id)
        if track_id is None:
            return []
        if keep:
            moved = th.copy_marks(marks, track_id, lambda: uuid.uuid4().hex[:8])
            self.marks.extend(moved)
        else:
            for m in marks:
                m["track_id"] = track_id
            moved = marks
        self._multi = [m["id"] for m in moved]
        self.selected = ("mark", moved[0]["id"])
        self._mark_changed()
        self.render_waveform()
        return moved

    def _track_submenu(self, menu, label, ids, keep):
        sub = tk.Menu(menu, tearoff=False, bg="#ffffff", fg="#1e1e1e")
        own = {(self.mark_by_id(i) or {}).get("track_id") for i in ids}
        for tr in self.tracks:
            sub.add_command(label=tr["name"], state="disabled" if tr["id"] in own and len(own) == 1 else "normal",
                            command=lambda t=tr["id"]: self.move_selection_to_track(t, ids, keep))
        if self.tracks:
            sub.add_separator()
        sub.add_command(label="New track...", command=lambda: self.move_selection_to_track("new", ids, keep))
        menu.add_cascade(label=label, menu=sub)

    def _add_clipboard_items(self, menu, ids):
        n = len(ids)
        what = f"{n} Marks" if n > 1 else "Mark"
        menu.add_command(label=f"Cut {what}", accelerator="Ctrl+X", command=lambda: self.cut_selection(ids))
        menu.add_command(label=f"Copy {what}", accelerator="Ctrl+C", command=lambda: self.copy_selection(ids))
        self._track_submenu(menu, f"Move {what} to Track", ids, keep=False)
        self._track_submenu(menu, f"Copy {what} to Track", ids, keep=True)

    def _add_paste_items(self, menu, track_id):
        n = len(_MARK_CLIPBOARD["marks"])
        state = "normal" if n else "disabled"
        what = f"{n} mark{'s' if n != 1 else ''}" if n else "marks"
        menu.add_separator()
        menu.add_command(label=f"Paste {what} here (same times)", accelerator="Ctrl+V", state=state,
                         command=lambda: self.paste_marks(track_id))
        menu.add_command(label=f"Paste {what} at @cursor", state=state,
                         command=lambda: self.paste_marks(track_id, at_cursor=True))

    # ------------------------------------------------------------------ card actions on selections
    def _after_menu(self, fn):
        """Run a menu's bigger action once the menu has closed."""
        try:
            self.canvas.after_idle(fn)
        except (tk.TclError, AttributeError):
            fn()

    def merge_selection(self, ids=None):
        """Merge the selected marks (one track) into one card, in time
        order -- remembering the originals for Unmerge. One undo step."""
        marks = sorted(self._selected_marks(ids), key=lambda m: (m["start"], m["id"]))
        if len(marks) < 2:
            return False
        first = marks[0]

        def run():
            for other in marks[1:]:
                start, end, label = th.merged_fields(first, other)
                first["pieces"] = th.merged_pieces(first, other)
                first["start"], first["end"], first["label"], first["type"] = start, end, label, "range"
                voices = th.merge_voice_lists(first.get("voices"), other.get("voices"))
                if voices:
                    first["voices"] = voices
                self.marks = [m for m in self.marks if m["id"] != other["id"]]
            self._multi = []
            self.selected = ("mark", first["id"])
            return True
        return self._one_step(run)

    def split_selection(self, how, ids=None):
        """Split each selected card: how = "half" | "words" | "cursor".
        One undo step for all of them."""
        marks = self._selected_marks(ids)
        if not marks:
            return 0
        pos = self.cursor_position()

        def run():
            done = 0
            for m in marks:
                label = m.get("label") or ""
                if how == "words":
                    spans = th.word_spans(label)
                    ok = len(spans) >= 2 and self.split_mark_into(m["id"], spans)
                elif how == "cursor":
                    ok = pos is not None and self.split_mark_by_id(m["id"], at_time=pos)
                else:
                    ok = self.split_mark_by_id(m["id"], at_time=-1.0)
                done += bool(ok)
            self._multi = []
            return done
        return self._one_step(run)

    def unmerge_selection(self, ids=None):
        marks = [m for m in self._selected_marks(ids) if len(m.get("pieces") or []) >= 2]
        return self._one_step(lambda: sum(bool(self.unmerge_mark_by_id(m["id"])[0]) for m in marks)) if marks else 0

    def _add_card_items(self, menu, ids):
        """Split / merge / unmerge for the selected card(s)."""
        marks = self._selected_marks(ids)
        if not marks:
            return
        pos = self.cursor_position()
        n = len(marks)
        if n == 1:
            m = marks[0]
            is_range = m["type"] == "range" and m.get("end") is not None
            inside = is_range and pos is not None and m["start"] + th.MIN_RANGE <= pos <= m["end"] - th.MIN_RANGE
            n_words = len(th.word_spans(m.get("label") or ""))
            menu.add_command(label="Split at @cursor", state="normal" if inside else "disabled",
                             command=lambda: self.split_selection("cursor", [m["id"]]))
            menu.add_command(label="Split in half", state="normal" if is_range else "disabled",
                             command=lambda: self.split_selection("half", [m["id"]]))
            menu.add_command(label=f"Split into words ({n_words})", state="normal" if n_words >= 2 else "disabled",
                             command=lambda: self.split_selection("words", [m["id"]]))
            pool = self.track_marks(m.get("track_id")) if m.get("track_id") else \
                [x for x in self.marks if x.get("track_id") is None]
            prev_m, next_m = th.neighbor_mark(pool, m, -1), th.neighbor_mark(pool, m, 1)
            menu.add_command(label="Merge with Previous", state="normal" if prev_m else "disabled",
                             command=lambda: self.merge_mark_by_id(m["id"], -1))
            menu.add_command(label="Merge with Next", state="normal" if next_m else "disabled",
                             command=lambda: self.merge_mark_by_id(m["id"], 1))
        else:
            menu.add_command(label=f"Merge {n} into One Card", command=lambda: self._after_menu(lambda: self.merge_selection(ids)))
            menu.add_command(label=f"Split Each at @cursor  (where it's inside)", state="normal" if pos is not None
                             else "disabled", command=lambda: self._after_menu(lambda: self.split_selection("cursor", ids)))
            menu.add_command(label="Split Each in Half", command=lambda: self._after_menu(lambda: self.split_selection("half", ids)))
            menu.add_command(label="Split Each into Words", command=lambda: self._after_menu(lambda: self.split_selection("words", ids)))
        merged = sum(1 for m in marks if len(m.get("pieces") or []) >= 2)
        if merged:
            label = (f"Unmerge into {len(marks[0]['pieces'])} Cards" if n == 1
                     else f"Unmerge {merged} Merged Card{'s' if merged != 1 else ''}")
            menu.add_command(label=label, command=lambda: self._after_menu(lambda: self.unmerge_selection(ids)))

    def _show_group_menu(self, ids, event):
        menu = tk.Menu(self.canvas, tearoff=False)
        menu.add_command(label=f"{len(ids)} marks selected", state="disabled")
        menu.add_separator()
        self._add_card_items(menu, ids)
        menu.add_separator()
        self._add_shift_items(menu, ids)
        menu.add_separator()
        self._add_clipboard_items(menu, ids)
        menu.add_separator()
        menu.add_command(label=f"Delete {len(ids)} Marks", command=lambda: self.delete_selection(ids))
        menu.tk_popup(event.x_root, event.y_root)

    def export_per_voice(self, track):
        marks = [m for m in self.marks if m.get("track_id") == track["id"]]
        if not marks:
            messagebox.showinfo("Export per Voice", f"Track \"{track['name']}\" has no timing marks to export.")
            return
        VoiceExportDialog(self.canvas, self, track, marks)

    # ------------------------------------------------------------------ copy track / renumber
    def copy_track(self, track):
        """A new track with copies of all of this track's marks (one undo step)."""
        names = [t["name"] for t in self.tracks]
        new = self._new_track(th.unique_track_name(f"{track['name']} copy", names), record_history=False)
        self.marks.extend(th.copy_marks(self.track_marks(track["id"]), new["id"], lambda: uuid.uuid4().hex[:8]))
        self.selected = ("track", new["id"])
        self._mark_changed()
        self.render_waveform()
        return new

    def _current_track_id(self):
        """The track being worked on: the selected track, the selected
        mark's track, or the one the card editor shows."""
        if self.selected:
            kind, sel_id = self.selected
            if kind == "track":
                return sel_id
            mark = self.mark_by_id(sel_id)
            if mark is not None:
                return mark.get("track_id")
        return self.panel_track_id() if hasattr(self, "panel_track_id") else None

    def select_end_mark(self, last=False):
        """Home / End on the waveform: the first / last mark of the current
        track (or of the unassigned marks when no track is current)."""
        track_id = self._current_track_id()
        pool = [m for m in self.marks if m.get("track_id") == track_id]
        if not pool:
            return None
        mark = (max if last else min)(pool, key=lambda m: (m["start"], m["id"]))
        self._multi = []
        self.select_mark(mark["id"])
        return mark

    def shift_marks(self, ids, seconds):
        """Move these marks by seconds (+ later, - earlier) as one block,
        one undo step. The amount is limited so none starts before 0:00 or
        ends past the allowed end (lengths kept). Returns the amount used."""
        marks = [m for m in (self.mark_by_id(i) for i in ids) if m is not None]
        if not marks or not seconds:
            return 0.0
        first = min(m["start"] for m in marks)
        last = max((m.get("end") if m.get("end") is not None else m["start"]) for m in marks)
        seconds = max(seconds, -first)
        seconds = min(seconds, self.max_mark_time() - last)
        if abs(seconds) < 1e-9:
            return 0.0
        for m in marks:
            m["start"] = round(m["start"] + seconds, 6)
            if m.get("end") is not None:
                m["end"] = round(m["end"] + seconds, 6)
            for p in m.get("pieces") or []:
                p["start"] = round(p["start"] + seconds, 6)
                if p.get("end") is not None:
                    p["end"] = round(p["end"] + seconds, 6)
        self._mark_changed()
        self.render_waveform()
        return seconds

    def _delta_to_cursor(self, ids):
        """Seconds that put the earliest of these marks' Start on the @cursor."""
        marks = [m for m in (self.mark_by_id(i) for i in ids) if m is not None]
        pos = self.cursor_position()
        if not marks or pos is None:
            return None
        return pos - min(m["start"] for m in marks)

    def shift_selection_to_cursor(self, ids=None):
        """The (first) selected mark starts at the @cursor; the other
        selected marks move by the same amount."""
        ids = self.selected_mark_ids() if ids is None else ids
        delta = self._delta_to_cursor(ids)
        if delta is None:
            return 0.0
        return self._report_shift(self.shift_marks(ids, delta), delta)

    def shift_track_to_cursor(self, track):
        """The whole track moves so its first selected mark (or its first
        mark) starts at the @cursor."""
        mine = [i for i in self.selected_mark_ids() if (self.mark_by_id(i) or {}).get("track_id") == track["id"]]
        ref = mine or [m["id"] for m in self.track_marks(track["id"])]
        delta = self._delta_to_cursor(ref)
        if delta is None:
            return 0.0
        return self._report_shift(self.shift_marks([m["id"] for m in self.track_marks(track["id"])], delta), delta)

    def _report_shift(self, done, wanted):
        if abs(done - wanted) > 1e-6:
            self.play_status_var.set(f"Shifted by {done:+.3f} s (limited by the start/end of the audio)")
        elif done:
            self.play_status_var.set(f"Shifted by {done:+.3f} s")
        return done

    def _ask_seconds(self, title, what):
        text = simpledialog.askstring(
            title, f"Move {what} by how many seconds?\n(positive = later, negative = earlier; e.g. 0.25 or -1.5)",
            initialvalue=str(get_preference("shift_track_seconds", "0.1")))
        if text is None:
            return None
        try:
            seconds = float(text.strip().replace(",", ".").rstrip("s").strip())
        except ValueError:
            messagebox.showinfo(title, f"Couldn\u2019t read \u201c{text}\u201d as seconds.")
            return None
        set_preference("shift_track_seconds", text.strip())
        return seconds

    def ask_shift_selection(self, ids=None):
        ids = self.selected_mark_ids() if ids is None else ids
        n = len(ids)
        seconds = self._ask_seconds("Shift Marks", f"the {n} selected mark{'s' if n != 1 else ''}")
        if seconds is None:
            return None
        return self._report_shift(self.shift_marks(ids, seconds), seconds)

    def _add_shift_items(self, menu, ids):
        n = len(ids)
        what = f"{n} Marks" if n > 1 else "Mark"
        at_ok = self.cursor_position() is not None
        menu.add_command(label=f"Shift {what} to @cursor" + ("  (first one starts there)" if n > 1 else ""),
                         state="normal" if at_ok else "disabled",
                         command=lambda: self.shift_selection_to_cursor(ids))
        menu.add_command(label=f"Shift {what}...", command=lambda: self.ask_shift_selection(ids))

    def show_selection_menu(self, event, ids=None):
        """Right-click on selected cards (card editor) or marks: what can be
        done with them -- shift, cut/copy/move/copy to a track, unmerge,
        delete."""
        ids = self.selected_mark_ids() if ids is None else ids
        if not ids:
            return None
        menu = tk.Menu(self.canvas, tearoff=False)
        n = len(ids)
        menu.add_command(label=f"{n} mark{'s' if n != 1 else ''} selected", state="disabled")
        menu.add_separator()
        self._add_card_items(menu, ids)
        menu.add_separator()
        self._add_shift_items(menu, ids)
        menu.add_separator()
        self._add_clipboard_items(menu, ids)
        menu.add_separator()
        menu.add_command(label=f"Delete {n} Mark{'s' if n != 1 else ''}", command=lambda: self.delete_selection(ids))
        try:
            menu.tk_popup(getattr(event, "x_root", 0), getattr(event, "y_root", 0))
        except tk.TclError:
            pass
        return menu

    def shift_track(self, track, seconds):
        """Move every mark of the track by seconds (+ later, - earlier), one
        undo step. Marks that would start before 0:00 are kept at 0:00
        (their length kept); the amount is limited so none ends past the
        allowed end."""
        return self.shift_marks([m["id"] for m in self.track_marks(track["id"])], seconds)

    def ask_shift_track(self, track):
        seconds = self._ask_seconds("Shift Track", f"every mark of \u201c{track['name']}\u201d")
        if seconds is None:
            return None
        return self._report_shift(self.shift_track(track, seconds), seconds)

    def renumber_from_mark(self, mark_id, first=None):
        """Bars/Beats-style tracks: relabel from this mark on, counting up
        from `first` (asked for); a Beats track's numbers wrap as before."""
        mark = self.mark_by_id(mark_id)
        if mark is None or not mark.get("track_id"):
            return False
        marks = sorted(self.track_marks(mark["track_id"]), key=lambda m: m["start"])
        labels = [m.get("label", "") for m in marks]
        cycle = th.numbering_cycle(labels)
        if cycle is None:
            return False
        if first is None:
            first = simpledialog.askinteger("Renumber", "Number for this mark (the ones after it count up"
                                            + (f", wrapping after {cycle}" if cycle else "") + "):",
                                            initialvalue=1, minvalue=0 if not cycle else 1,
                                            maxvalue=cycle or 1000000)
            if first is None:
                return False
        new = th.renumber_from(labels, marks.index(mark), int(first), cycle or 0)
        for m, label in zip(marks, new):
            m["label"] = label
        self._mark_changed()
        self.render_waveform()
        return True

    # ------------------------------------------------------------------ bars / beats
    BEAT_TRACK_NAMES = {"beats": "Beats", "bars": "Bars"}

    BEAT_LENGTH_CHOICES = (("fill", "Up to the next mark (touching)"),
                           ("beat", "One beat"),
                           ("lines", "No length (lines)"))

    def beat_length(self):
        value = get_preference("beats_length", "fill")
        return value if value in dict(self.BEAT_LENGTH_CHOICES) else "fill"

    def beat_labels(self):
        return bool(get_preference("beats_labels", True))

    def _styled_specs(self, specs, beats=None, end=None):
        return th.style_beat_marks(specs, self.beat_length(), self.beat_labels(), beats=beats, end=end)

    def beats_per_bar(self):
        try:
            return max(1, min(16, int(get_preference("beats_per_bar", 4))))
        except (TypeError, ValueError):
            return 4

    def _beats_submenu(self, key):
        """The Beats menu's cascades, made once and refilled on each open
        (a new tk.Menu per open piled up hidden menus)."""
        subs = self.__dict__.setdefault("_beats_subs", {})
        sub = subs.get(key)
        if sub is None:
            sub = tk.Menu(self.beats_menu, tearoff=False, bg="#ffffff", fg="#1e1e1e",
                          activebackground="#cce4ff", activeforeground="#1e1e1e",
                          disabledforeground="#9a9a9a", selectcolor="#1e1e1e")
            subs[key] = sub
        try:
            sub.delete(0, "end")
        except tk.TclError:
            pass
        return sub

    def _reopen_menu(self, button, menu):
        """Show a toolbar menu again right below its button. Tk closes a
        menu on every click; an option (checkbox / radio choice) calls this
        so the menu stays up until an action is picked or the user clicks
        elsewhere (tk_popup takes the grab, so an outside click closes it)."""
        def go():
            try:
                x = button.winfo_rootx()
                y = button.winfo_rooty() + button.winfo_height()
                menu.tk_popup(x, y)
            except (tk.TclError, AttributeError):
                pass
        self._after_menu(go)

    def _menu_option(self, button, menu, fn):
        """A menu command for an option: apply it, keep the menu open."""
        def run():
            fn()
            self._reopen_menu(button, menu)
        return run

    def _beats_pick(self, label, fn, *args):
        """A Beats menu command: logged, then run once the menu has closed
        (its grab released) so dialogs and the busy state behave."""
        def run():
            debug(2, f"beats menu: '{label}' picked")
            fn(*args)
        return lambda: self._after_menu(run)

    def _fill_beats_menu(self):
        menu = self.beats_menu
        try:
            menu.delete(0, "end")
        except tk.TclError:
            pass
        bpb = self.beats_per_bar()
        have = aa.beats_available()
        need = "" if have else "  (needs librosa)"
        state = "normal" if have else "disabled"
        menu.add_command(label="All beats" + need, state=state,
                         command=self._beats_pick("All beats", self.run_beats, "beats"))
        menu.add_command(label="Downbeats (beat 1)" + need, state=state,
                         command=self._beats_pick("Downbeats", self.run_beats, "beat", 1))
        sub = self._beats_submenu("beat_n")
        for n in range(2, bpb + 1):
            sub.add_command(label=f"Beat {n}", command=self._beats_pick(f"Beat {n}", self.run_beats, "beat", n))
        menu.add_cascade(label="Beat N of each bar" + need, menu=sub, state=state if bpb > 1 else "disabled")
        menu.add_command(label="Bars (numbered)" + need, state=state,
                         command=self._beats_pick("Bars", self.run_beats, "bars"))
        menu.add_separator()
        menu.add_command(label="Metronome...", command=self._beats_pick("Metronome", self.run_metronome))
        menu.add_separator()
        per_bar = self._beats_submenu("per_bar")
        if getattr(self, "_bpb_var", None) is None:
            self._bpb_var = tk.IntVar(value=bpb)
        self._bpb_var.set(bpb)
        for n in (2, 3, 4, 5, 6, 7, 8, 12):
            per_bar.add_radiobutton(label=str(n), variable=self._bpb_var, value=n,
                                    command=self._menu_option(self.beats_btn, menu,
                                                              lambda k=n: set_preference("beats_per_bar", k)))
        menu.add_cascade(label=f"Beats per bar: {bpb}", menu=per_bar)
        where = self._beats_submenu("where")
        if getattr(self, "_beat_scope_var", None) is None:
            self._beat_scope_var = tk.StringVar(value=self.beat_scope())
        self._beat_scope_var.set(self.beat_scope())
        for key, label in self.BEAT_SCOPES:
            where.add_radiobutton(label=label, variable=self._beat_scope_var, value=key,
                                  command=self._menu_option(self.beats_btn, menu,
                                                            lambda k=key: set_preference("beats_scope", k)))
        menu.add_cascade(label="Where: " + dict(self.BEAT_SCOPES)[self.beat_scope()], menu=where)
        length = self._beats_submenu("length")
        if getattr(self, "_beat_length_var", None) is None:
            self._beat_length_var = tk.StringVar(value=self.beat_length())
        self._beat_length_var.set(self.beat_length())
        for key, label in self.BEAT_LENGTH_CHOICES:
            length.add_radiobutton(label=label, variable=self._beat_length_var, value=key,
                                   command=self._menu_option(self.beats_btn, menu,
                                                             lambda k=key: set_preference("beats_length", k)))
        menu.add_cascade(label="Length: " + dict(self.BEAT_LENGTH_CHOICES)[self.beat_length()], menu=length)
        if getattr(self, "_beat_labels_var", None) is None:
            self._beat_labels_var = tk.BooleanVar(value=self.beat_labels())
        self._beat_labels_var.set(self.beat_labels())
        menu.add_checkbutton(label="Label the marks (beat / bar numbers)", variable=self._beat_labels_var,
                             command=self._menu_option(self.beats_btn, menu, lambda: set_preference(
                                 "beats_labels", bool(self._beat_labels_var.get()))))
        if not have:
            menu.add_command(label="Install librosa: \u26a0 Install button (upper right)", state="disabled")

    def analysis_range(self):
        """The selected range mark's span, else @cursor .. the end."""
        return self.analysis_range_why()[:2]

    BEAT_SCOPES = (("auto", "The selected range, else the whole song"),
                   ("cursor", "From the @cursor to the end"),
                   ("all", "The whole song"))

    def beat_scope(self):
        value = get_preference("beats_scope", "auto")
        return value if value in dict(self.BEAT_SCOPES) else "auto"

    def analysis_range_why(self, scope="cursor"):
        """(start, end, where it came from) -- for messages. scope:
        "cursor" = the selected range, else @cursor .. end (Transcribe);
        "auto" = the selected range, else the whole song;
        "all" = the whole song (ignores the selection)."""
        if scope == "all":
            return 0.0, self.audio_duration or 0.0, "the whole song"
        mark = self.mark_by_id(self.selected_mark_id())
        if scope != "all" and mark and mark["type"] == "range" and mark.get("end") is not None:
            label = (mark.get("label") or "").strip()
            what = f"the selected {'card' if mark.get('track_id') else 'range'}" + (
                f" \u201c{label[:30]}\u201d" if label else "")
            return mark["start"], mark["end"], what
        if scope == "auto":
            return 0.0, self.audio_duration or 0.0, "the whole song"
        start = self.cursor_position() or 0.0
        return start, self.audio_duration or start, "from the @cursor to the end"

    def _beat_track_name(self, mode, which=1, interval=None):
        if mode == "beat":
            base = "Downbeats" if which == 1 else f"Beat {which}"
        elif mode == "metronome":
            bpm = 60.0 / interval
            base = f"Metronome {bpm:.0f} BPM" if abs(bpm - round(bpm)) < 0.05 else f"Metronome {interval:g} s"
        else:
            base = self.BEAT_TRACK_NAMES[mode]
        return th.unique_track_name(base, [t["name"] for t in self.tracks])

    def _add_marks_track(self, name, specs, source="beats"):
        """One new track holding these {start, end, label} marks (one undo step)."""
        track = self._new_track(name, record_history=False)
        for sp in specs:
            end = sp.get("end")
            self.marks.append({"id": uuid.uuid4().hex[:8], "type": "range" if end is not None else "point",
                               "start": sp["start"], "end": end, "label": sp["label"], "track_id": track["id"],
                               "source": source})
        self.selected = ("track", track["id"])
        self._mark_changed()
        self.render_waveform()
        return track

    def run_beats(self, mode, which=1):
        """Detect beats (once per file; cached while it's open), then make
        a track for the range (selected range, or @cursor to the end)."""
        debug(2, f"beats: run mode={mode} which={which} busy={self._analysis_busy} "
                 f"duration={self.audio_duration} librosa={aa.beats_available()}")
        if self._analysis_busy:
            self.announce(f"Beats: wait until the running job ({self._analysis_busy}) has finished")
            return
        if self.audio_duration is None:
            self.announce("Beats: no audio loaded yet")
            return
        if not aa.beats_available():
            messagebox.showinfo("Beats", "Beat detection needs librosa, which isn't installed.\n\n"
                                         "Use the \u26a0 Install button in the upper right corner.")
            return
        start, end, self._beat_range_why = self.analysis_range_why(self.beat_scope())
        cached = getattr(self, "_beat_cache", None)
        try:
            st = Path(self.filepath).stat()
            stamp = (st.st_mtime, st.st_size)
        except OSError:
            stamp = None
        if cached and cached.get("stamp") == stamp:
            return self._make_beat_track(cached["result"], mode, which, start, end)
        self._set_analysis_busy("beats")
        self.append_info("\n{yellow}Finding beats in the background...\n")

        def work(progress):
            return aa.detect_beats(self.filepath, progress)

        def done(result, error, elapsed):
            self._set_analysis_busy(None)
            self.analysis_status_var.set("")
            if error is not None:
                self.append_info("{red}Beat detection error: " + _explained(error, "Beat detection") + "\n")
                debug(1, f"{{red}}waveform_tab beats failed: {error}")
                self.announce("Beats: detection failed -- see the text panel")
                self._show_text_panel()
                return
            self._beat_cache = {"stamp": stamp, "result": result}
            self.append_info(f"{{green}}Found {len(result['beats'])} beats, about {result['tempo']:.0f} BPM "
                             f"({elapsed:.1f}s).\n")
            self._make_beat_track(result, mode, which, start, end)
        self._run_in_thread(work, done, progress_prefix="Beats: ")

    def _make_beat_track(self, result, mode, which, start, end):
        bpb = self.beats_per_bar()
        phase = th.downbeat_phase(result["strength"], result["bass"], bpb)
        specs = th.beat_marks(result["beats"], start, end, bpb, phase, mode, which)
        specs = self._styled_specs(specs, beats=result["beats"], end=end)
        in_range = sum(1 for t in result["beats"] if start - 1e-9 <= t < end)
        why = getattr(self, "_beat_range_why", "")
        debug(2, f"beats: mode={mode} which={which} range {start:.3f}-{end:.3f} ({why}); "
                 f"{len(result['beats'])} beats, {in_range} in range, phase {phase}, {len(specs)} marks")
        if not specs:
            span = f"{th.format_time_ms(start)}\u2013{th.format_time_ms(end)}"
            if in_range == 0:
                reason = f"none of the {len(result['beats'])} beats is in {span} ({why})"
            else:
                reason = (f"{in_range} beat{'s' if in_range != 1 else ''} in {span} ({why}), but no "
                          f"{'bar start' if mode == 'bars' else f'beat {which}'} among them")
            self.append_info(f"{{yellow}}No track made: {reason}. Select nothing (Esc) and try again, or pick "
                             "Where \u25b8 The whole song in the Beats menu.\n")
            self.announce("Beats: no track made -- see the text panel")
            self._show_text_panel()
            return None
        track = self._add_marks_track(self._beat_track_name(mode, which), specs)
        self.append_info(f"{{blue}}Track \u201c{track['name']}\u201d: {len(specs)} marks "
                         f"({th.format_time_ms(start)}\u2013{th.format_time_ms(end)}, {bpb} beats per bar). "
                         "Which beat starts a bar is a guess: right-click a mark > Renumber from Here.\n")
        self.announce(f"Beats: new track \u201c{track['name']}\u201d ({len(specs)} marks)")
        return track

    # ------------------------------------------------------------------ Structure
    STRUCTURE_NAMES = (("guess", "Guessed (Intro, Verse, Chorus...)"),
                       ("letters", "Letters only (A, B, C...)"),
                       ("both", "Both (Verse 1 \u00b7 A)"))
    STRUCTURE_BARS = (2, 4, 8, 16)
    STRUCTURE_TRACK_NAME = "Structure"

    def structure_names(self):
        value = get_preference("structure_names", "guess")
        return value if value in dict(self.STRUCTURE_NAMES) else "guess"

    def structure_bars(self):
        try:
            value = int(get_preference("structure_min_bars", 4))
        except (TypeError, ValueError):
            value = 4
        return value if value in self.STRUCTURE_BARS else 4

    def _structure_submenu(self, key):
        subs = self.__dict__.setdefault("_structure_subs", {})
        sub = subs.get(key)
        if sub is None:
            sub = tk.Menu(self.structure_menu, tearoff=False, bg="#ffffff", fg="#1e1e1e",
                          activebackground="#cce4ff", activeforeground="#1e1e1e",
                          disabledforeground="#9a9a9a", selectcolor="#1e1e1e")
            subs[key] = sub
        try:
            sub.delete(0, "end")
        except tk.TclError:
            pass
        return sub

    def _fill_structure_menu(self):
        menu = self.structure_menu
        try:
            menu.delete(0, "end")
        except tk.TclError:
            pass
        have = aa.structure_available()
        menu.add_command(label="Find sections \u2192 new \u201cStructure\u201d track" + ("" if have else "  (needs librosa)"),
                         state="normal" if have else "disabled",
                         command=self._beats_pick("Structure", self.run_structure))
        menu.add_separator()
        names = self._structure_submenu("names")
        if getattr(self, "_structure_names_var", None) is None:
            self._structure_names_var = tk.StringVar(value=self.structure_names())
        self._structure_names_var.set(self.structure_names())
        for key, label in self.STRUCTURE_NAMES:
            names.add_radiobutton(label=label, variable=self._structure_names_var, value=key,
                                  command=self._menu_option(self.structure_btn, menu,
                                                            lambda k=key: set_preference("structure_names", k)))
        menu.add_cascade(label="Names: " + dict(self.STRUCTURE_NAMES)[self.structure_names()], menu=names)
        bars = self._structure_submenu("bars")
        if getattr(self, "_structure_bars_var", None) is None:
            self._structure_bars_var = tk.IntVar(value=self.structure_bars())
        self._structure_bars_var.set(self.structure_bars())
        for n in self.STRUCTURE_BARS:
            bars.add_radiobutton(label=f"{n} bars", variable=self._structure_bars_var, value=n,
                                 command=self._menu_option(self.structure_btn, menu,
                                                           lambda k=n: set_preference("structure_min_bars", k)))
        menu.add_cascade(label=f"Shortest section: {self.structure_bars()} bars", menu=bars)
        menu.add_command(label=f"Beats per bar: {self.beats_per_bar()}  (set in Beats \u25be)", state="disabled")
        if not have:
            menu.add_command(label="Install librosa: \u26a0 Install button (upper right)", state="disabled")

    def _file_stamp(self):
        try:
            st = Path(self.filepath).stat()
            return (st.st_mtime, st.st_size)
        except OSError:
            return None

    def run_structure(self):
        """Analyze the whole song (once per file while it's open), then
        make a "Structure" track of its sections."""
        debug(2, f"structure: run busy={self._analysis_busy} duration={self.audio_duration}")
        if self._analysis_busy:
            self.announce(f"Structure: wait until the running job ({self._analysis_busy}) has finished")
            return
        if self.audio_duration is None:
            self.announce("Structure: no audio loaded yet")
            return
        if not aa.structure_available():
            messagebox.showinfo("Structure", "Finding sections needs librosa, which isn't installed.\n\n"
                                             "Use the \u26a0 Install button in the upper right corner.")
            return
        stamp = self._file_stamp()
        cached = getattr(self, "_structure_cache", None)
        if cached and cached.get("stamp") == stamp:
            return self._make_structure_track(cached["result"])
        self._set_analysis_busy("structure")
        self.append_info("\n{yellow}Finding the song's sections in the background...\n")

        def work(progress):
            return aa.structure_features(self.filepath, progress)

        def done(result, error, elapsed):
            self._set_analysis_busy(None)
            self.analysis_status_var.set("")
            if error is not None:
                self.append_info("{red}Structure analysis error: " + _explained(error, "Structure analysis") + "\n")
                debug(1, f"{{red}}waveform_tab structure failed: {error}")
                self.announce("Structure: analysis failed -- see the text panel")
                self._show_text_panel()
                return
            self._structure_cache = {"stamp": stamp, "result": result}
            # the beats come for free: Beats \u25be reuses them
            self._beat_cache = {"stamp": stamp, "result": {k: result[k] for k in ("tempo", "beats", "strength", "bass")}}
            self.append_info(f"{{green}}Analyzed {len(result['beats'])} beats, about {result['tempo']:.0f} BPM "
                             f"({elapsed:.1f}s).\n")
            self._make_structure_track(result)
        self._run_in_thread(work, done, progress_prefix="Structure: ")

    def _vocal_fraction(self, start, end):
        """Share of [start, end) with vocals in the stem regions (None if
        stems haven't been separated)."""
        if not self.regions or end <= start:
            return None
        sung = 0.0
        for r in self.regions:
            if r.get("kind") in ("vocal", "mixed"):
                sung += max(0.0, min(end, r["end"]) - max(start, r["start"]))
        return sung / (end - start)

    def structure_specs(self, result):
        """{start, end, label} per section from structure_features()."""
        beats = result["beats"]
        n = len(beats)
        bpb = self.beats_per_bar()
        phase = th.downbeat_phase(result["strength"], result["bass"], bpb)
        downbeats = [i for i in range(n) if (i - phase) % bpb == 0]
        min_beats = max(4, self.structure_bars() * bpb)
        found = aa.find_sections(result["features"], downbeats, min_beats=min_beats)
        bounds, letters = found["bounds"], found["letters"]
        end_time = self.audio_duration or (beats[-1] if beats else 0.0)
        specs, energy, vocal = [], [], []
        rms = result.get("rms") or [1.0] * n
        for i in range(len(letters)):
            a, b = bounds[i], bounds[i + 1]
            start = 0.0 if i == 0 else beats[a]
            stop = end_time if i == len(letters) - 1 else beats[b]
            if stop - start < th.MIN_RANGE:
                continue
            specs.append({"start": start, "end": stop, "letter": letters[i]})
            energy.append(sum(rms[a:b]) / max(1, b - a))
            vocal.append(self._vocal_fraction(start, stop))
        names = aa.name_sections([sp["letter"] for sp in specs], energy, vocal)
        style = self.structure_names()
        for sp, name in zip(specs, names):
            sp["label"] = (sp["letter"] if style == "letters"
                           else f"{name} \u00b7 {sp['letter']}" if style == "both" else name)
        return specs

    def _make_structure_track(self, result):
        specs = self.structure_specs(result)
        if not specs:
            self.append_info("{yellow}No sections found (the song may be too short).\n")
            self.announce("Structure: no sections found -- see the text panel")
            self._show_text_panel()
            return None
        name = th.unique_track_name(self.STRUCTURE_TRACK_NAME, [t["name"] for t in self.tracks])
        track = self._add_marks_track(name, [{"start": sp["start"], "end": sp["end"], "label": sp["label"]}
                                             for sp in specs], source="structure")
        lines = "".join(f"{{cyan}}  {th.format_time_ms(sp['start'])}\u2013{th.format_time_ms(sp['end'])}  "
                        f"{{blue}}{sp['letter']}  {{cyan}}{sp['label']}\n" for sp in specs)
        self.append_info(f"{{blue}}Track \u201c{track['name']}\u201d: {len(specs)} sections "
                         f"(shortest {self.structure_bars()} bars; same letter = the music repeats). "
                         "The names are a guess -- edit them in the cards.\n" + lines)
        self.announce(f"Structure: new track \u201c{track['name']}\u201d ({len(specs)} sections)")
        return track

    def run_metronome(self, text=None):
        """Evenly spaced ticks at an interval the user types (seconds or BPM)."""
        if self.audio_duration is None:
            return None
        if text is None:
            text = simpledialog.askstring("Metronome", "Interval: seconds (e.g. 0.5) or BPM (e.g. 120 bpm):",
                                          initialvalue=str(get_preference("metronome_interval", "120 bpm")))
            if text is None:
                return None
        interval = th.parse_interval(text)
        if interval is None:
            messagebox.showinfo("Metronome", f"Couldn't read \u201c{text}\u201d. Try 0.5, 500 ms or 120 bpm.")
            return None
        set_preference("metronome_interval", text.strip())
        start, end, _why = self.analysis_range_why(self.beat_scope())
        specs = th.metronome_marks(start, end, interval, self.beats_per_bar())
        specs = self._styled_specs(specs, end=end)
        if not specs:
            self.append_info(f"{{yellow}}Metronome: no ticks between {th.format_time_ms(start)} and "
                             f"{th.format_time_ms(end)} ({_why}).\n")
            self.announce("Metronome: no track made -- see the text panel")
            self._show_text_panel()
            return None
        track = self._add_marks_track(self._beat_track_name("metronome", interval=interval), specs)
        self.announce(f"Metronome: new track \u201c{track['name']}\u201d ({len(specs)} marks)")
        return track

    def _show_track_menu(self, track, event):
        menu = tk.Menu(self.canvas, tearoff=False)
        menu.add_command(label="Rename Track...", command=lambda: self._rename_track(track))
        menu.add_command(label="Change Color...", command=lambda: self._change_track_color(track))
        menu.add_command(label="Copy Track", command=lambda: self.copy_track(track))
        menu.add_command(label="Shift Track...", command=lambda: self.ask_shift_track(track))
        menu.add_command(label="Shift Track to @cursor  (its first selected mark starts there)",
                         state="normal" if self.cursor_position() is not None else "disabled",
                         command=lambda: self.shift_track_to_cursor(track))
        sel = [i for i in self.selected_mark_ids() if (self.mark_by_id(i) or {}).get("track_id") == track["id"]]
        if sel:
            self._add_shift_items(menu, sel)
        menu.add_separator()
        menu.add_command(label="Export Combined...", command=lambda: self.export_timing_track(track))
        menu.add_command(label="Export per Voice...", command=lambda: self.export_per_voice(track))
        self._add_paste_items(menu, track["id"])
        menu.add_separator()
        menu.add_command(label="Delete Track", command=lambda: self._delete_track(track))
        menu.tk_popup(event.x_root, event.y_root)

    # ------------------------------------------------------------------ rendering
    def _render_grid(self, x_of, w, h, mid_y, amplitude_px):
        c = self.canvas
        db_step = th.db_grid_step(amplitude_px)
        floor_db = min(60, db_step * 8)
        db = 0
        while db >= -floor_db:
            amp = 10 ** (db / 20)
            y_top = mid_y - amp * amplitude_px
            y_bot = mid_y + amp * amplitude_px
            c.create_line(0, y_top, w, y_top, fill="#7a7a7a", dash=(3, 2))
            c.create_line(0, y_bot, w, y_bot, fill="#7a7a7a", dash=(3, 2))
            c.create_text(2, y_top, text=f"{db} dB", fill="#39ff14", anchor="sw", font=("TkDefaultFont", 7, "bold"))
            db -= db_step

        span = self.view_end - self.view_start
        if span > 0:
            interval = th.time_grid_interval(span)
            t = int(self.view_start / interval) * interval
            guard = 0
            while t <= self.view_end and guard < 200:
                if t >= self.view_start:
                    x = x_of(t)
                    c.create_line(x, 0, x, h, fill="#7a7a7a", dash=(3, 2))
                    c.create_text(x + 2, h - 16, text=th.format_time_ms(t), fill="#bbbbbb", anchor="sw",
                                  font=("TkDefaultFont", 7))
                t += interval
                guard += 1

    def _lane_epsilon(self, w):
        span = self.view_end - self.view_start
        if not w or span <= 0:
            return 0.0
        return 16.0 * span / w

    def _marks_with_lanes(self, pool, w):
        visible = []
        for m in pool:
            if m["type"] == "point":
                if self.view_start <= m["start"] <= self.view_end:
                    visible.append(m)
            else:
                if m["end"] >= self.view_start and m["start"] <= self.view_end:
                    visible.append(m)
        visible.sort(key=lambda m: m["start"])
        items = [(m["start"], m["end"] if m["type"] == "range" else m["start"], m["id"]) for m in visible]
        lanes = th.assign_lanes(items, self._lane_epsilon(w))
        lane_count = (max(lanes.values()) + 1) if lanes else 1
        return visible, lanes, lane_count

    def _view_state(self):
        """What's remembered between sessions: the selection and the
        waveform's zoom/scroll (rounded to the millisecond)."""
        return (self.selected, tuple(self.selected_mark_ids()), round(self.view_start, 3), round(self.view_end, 3))

    def _remember_selection_later(self):
        """Selection or zoom/scroll changed: it's saved to the sidecar
        (keys "selection" and "view") with the next save -- File > Save or
        auto-save -- or on its own once the auto-save interval has passed,
        and when the tab/app closes; so reopening the file comes back to
        the same track or card, zoom and position. This alone doesn't mark
        the tab unsaved."""
        if self.audio_duration is None:
            return                       # still loading: nothing to remember yet
        state = self._view_state()
        if state == getattr(self, "_remembered_state", None):
            return
        self._remembered_state = state
        if getattr(self, "_remember_after", None) is not None:
            return                       # already scheduled: it saves whatever is current then
        interval = get_autosave_seconds()
        if interval > 0:
            try:
                self._remember_after = self.canvas.after(int(interval * 1000), self.remember_selection)
            except tk.TclError:
                pass
        else:
            self._selection_unsaved = True      # saved with the next explicit save / on close

    def _cancel_remember(self):
        pending = getattr(self, "_remember_after", None)
        self._remember_after = None
        if pending is not None:
            try:
                self.canvas.after_cancel(pending)
            except (tk.TclError, ValueError):
                pass

    def remember_selection(self):
        self._cancel_remember()
        self._selection_unsaved = False
        if self.audio_duration is None:
            return
        sel = list(self.selected) if self.selected and self.selected[0] in ("track", "mark") else None
        group = self.selected_mark_ids()
        th.update_cache(self.filepath, selection=sel, selection_group=group if len(group) > 1 else None,
                        view=[round(self.view_start, 3), round(self.view_end, 3)])

    def restore_view(self):
        """Reopening a file: the zoom and scroll position it had (if still
        valid for this audio). Returns True if restored."""
        view = th.load_cache(self.filepath).get("view")
        try:
            start, end = float(view[0]), float(view[1])
        except (TypeError, ValueError, IndexError):
            return False
        limit = (self.audio_duration or 0.0) * self.OVERSHOOT_FACTOR
        if not (0.0 <= start < end <= limit + 1e-6) or end - start < 0.01:
            return False
        self.view_start, self.view_end = start, end
        self._refresh_view_from_cache(render=False)
        return True

    def selection_needs_saving(self):
        return getattr(self, "_remember_after", None) is not None or getattr(self, "_selection_unsaved", False)

    def restore_selection(self, reveal=True):
        crumb("waveform restore selection")
        return self._restore_selection(reveal)

    def _restore_selection(self, reveal=True):
        """Reopening a file: select the track or card that was selected
        when it was last open (and, with reveal, bring it into view --
        not when last session's zoom/scroll was restored)."""
        cache = th.load_cache(self.filepath)
        saved = cache.get("selection")
        if not saved or len(saved) != 2:
            return False
        kind, ident = saved
        if kind == "mark" and self.mark_by_id(ident) is not None:
            self.selected = ("mark", ident)
            group = [i for i in (cache.get("selection_group") or []) if self.mark_by_id(i) is not None]
            self._multi = group if ident in group and len(group) > 1 else []
            if reveal:
                self._ensure_mark_visible(self.mark_by_id(ident))
        elif kind == "track" and self.track_by_id(ident) is not None:
            self.selected = ("track", ident)
        else:
            return False
        self._remembered_state = self._view_state()
        self.render_waveform()
        if self.panel is not None:
            try:
                self.canvas.after_idle(self.panel.scroll_to_selected)
            except tk.TclError:
                pass
        return True

    # What Shift / Ctrl do on the waveform, shown while the key is held
    # (the toolbar's buttons show theirs by changing color).
    MODIFIER_HINTS = {
        "shift": "Shift: click = range from the last click / @cursor   \u00b7   drag a mark = no snapping",
        "control": "Ctrl: click / drag = move the @cursor only",
    }

    def _show_modifier_hint(self, held):
        self._mod_hint = next((self.MODIFIER_HINTS[m] for m in ("control", "shift") if m in held), None)
        self._draw_modifier_hint()

    def _draw_modifier_hint(self):
        c = self.canvas
        try:
            c.delete("modhint")
            hint = getattr(self, "_mod_hint", None)
            if hint and not getattr(self, "closing", False):
                color = MOD_HINT_COLORS["control" if hint.startswith("Ctrl") else "shift"]
                layout = self._track_layout()
                y = (layout["row_top"] + layout["track_top"]) / 2      # the status row, under the waveform
                w = self._canvas_size()[0]
                bg = c.create_rectangle(w - 6, y - 8, w - 6, y + 8, fill="#000000", outline="", tags=("modhint",))
                item = c.create_text(w - 10, y, text=hint, anchor="e", fill=color,
                                     font=("TkDefaultFont", 9, "bold"), tags=("modhint",))
                try:                       # a dark backing so it reads over the region key
                    x0, y0, x1, y1 = c.bbox(item)
                    c.coords(bg, x0 - 4, y0 - 1, x1 + 4, y1 + 1)
                except (tk.TclError, TypeError, ValueError):
                    pass
        except tk.TclError:
            raise                  # canvas gone: utils drops this listener

    def teardown(self):
        """The app is closing (tab.teardown_hook): stop playback and timers
        and drop the card widgets in one go, so nothing redraws or
        re-lays-out while Tk takes the window apart."""
        self.closing = True
        try:
            if self._play_state != "stopped":
                self._halt_engine()
        except Exception:
            pass
        self._play_state = "stopped"
        self._cancel_remember()
        if self.panel is not None:
            self.panel.teardown()

    def render_waveform(self):
        if getattr(self, "closing", False):
            return
        if getattr(self, "_batch_depth", 0):
            return                         # _one_step draws once when the whole batch is done
        crumb("waveform render")
        self._remember_selection_later()
        c = self.canvas
        c.delete("all")
        w = self._canvas_size()[0]
        layout = self._track_layout()
        h = layout["work_height"]
        mid_y = h // 2
        amplitude_px = mid_y - 10
        span = self.view_end - self.view_start

        if self.audio_duration is not None:
            self._update_time_readout()

        def x_of(t):
            if span <= 0:
                return 0
            return (t - self.view_start) / span * w

        self._render_grid(x_of, w, h, mid_y, amplitude_px)

        work_marks = [m for m in self.marks if m.get("track_id") is None]
        visible_work, work_lanes, work_lane_count = self._marks_with_lanes(work_marks, w)
        lane_h = h / work_lane_count
        for m in visible_work:
            if m["type"] != "range":
                continue
            x1 = x_of(max(m["start"], self.view_start))
            x2 = x_of(min(m["end"], self.view_end))
            lane = work_lanes[m["id"]]
            c.create_rectangle(x1, lane * lane_h, x2, (lane + 1) * lane_h, fill="#2e4a63", outline="")
        if self._preview_range:
            ps, pe = self._preview_range
            if pe >= self.view_start and ps <= self.view_end:
                x1 = x_of(max(ps, self.view_start))
                x2 = x_of(min(pe, self.view_end))
                c.create_rectangle(x1, 0, x2, h, fill="#4a4a2e", outline="")

        n = len(self.peaks)
        if n == 0:
            c.create_text(w // 2, mid_y, text="(no waveform data)", fill="#888888")
        else:
            use_regions = bool(self.regions) and span > 0
            p0, p1 = getattr(self, "_peaks_span", None) or (self.view_start, self.view_end)
            pspan = max(1e-9, p1 - p0)
            for i, (mn, mx) in enumerate(self.peaks):
                t = p0 + (i + 0.5) / n * pspan
                x = int(x_of(p0 + i / n * pspan))
                y1 = mid_y - mx * amplitude_px
                y2 = mid_y - mn * amplitude_px
                color = WAVE_COLOR
                if use_regions:
                    color = self.region_colors.get(self._region_kind_at(t), WAVE_COLOR)
                c.create_line(x, y1, x, y2, fill=color)
        if self.audio_duration is not None and self.view_end > self.audio_duration:
            # shade the part of the view past the end of the audio
            x_end = x_of(self.audio_duration)
            c.create_rectangle(x_end, 0, w, h, fill="#141414", outline="", tags=("past_end",))
            c.create_line(x_end, 0, x_end, h, fill="#5a5a5a")


        self._render_marks(x_of, w, h, visible_work, work_lanes, work_lane_count)
        self._render_tracks(x_of, w, layout)
        self._render_drag_preview(w, layout)
        self._render_cursor(x_of, layout)
        self._render_playhead(x_of, layout)
        self._render_time_readout(w)
        self._draw_modifier_hint()
        if self.panel is not None:
            try:
                self.panel.sync()
            except tk.TclError:
                pass

    def _render_marks(self, x_of, w, h, visible, lanes, lane_count):
        self._mark_hit_regions = {}
        lane_h = h / lane_count

        labeled = [m for m in visible if m["label"]]
        labeled_pos = {m["id"]: i for i, m in enumerate(labeled)}

        def label_width_limit(mark):
            i = labeled_pos.get(mark["id"])
            if i is None:
                return w
            if i + 1 < len(labeled):
                return x_of(labeled[i + 1]["start"])
            return w

        c = self.canvas
        for m in visible:
            is_sel = self._is_highlighted("mark", m["id"])
            color = self.SELECTION_COLOR if is_sel else ("#ff9800" if m["type"] == "range" else "#ff3b3b")
            width = 2 if is_sel else 1
            x1 = x_of(max(m["start"], self.view_start))
            tag = f"mark_{m['id']}"
            text_tag = f"marktext_{m['id']}"
            lane = lanes[m["id"]]
            y0, y1 = lane * lane_h, (lane + 1) * lane_h

            c.create_line(x1, y0, x1, y1, fill=color, width=width, tags=(tag,))
            if m["type"] == "range":
                x2 = x_of(min(m["end"], self.view_end))
                c.create_line(x2, y0, x2, y1, fill=color, width=width, tags=(tag,))
                ts_text = f"{th.format_time_ms(m['start'])} - {th.format_time_ms(m['end'])}"
            else:
                ts_text = th.format_time_ms(m["start"])

            c.create_text(x1 + 3, y0 + 2, text=ts_text, fill=color, anchor="nw",
                          font=("TkDefaultFont", 7, "bold"), tags=(tag, text_tag))
            if m["label"]:
                allotted = max(20, label_width_limit(m) - (x1 + 3))
                c.create_text(x1 + 3, y0 + 13, text=th.strip_adjustments(m["label"]).replace("\n", " / "),
                              fill="#ffffff", anchor="nw",
                              width=allotted, font=("TkDefaultFont", 7), tags=(tag, text_tag))
            self._mark_hit_regions[m["id"]] = c.bbox(text_tag)

    def _render_tracks(self, x_of, w, layout):
        c = self.canvas
        work_height = layout["work_height"]
        track_top = layout["track_top"]

        c.create_line(0, work_height, w, work_height, fill="#000000")

        self._track_label_regions = {}
        self._track_band_regions = {}

        for i, tr in enumerate(self.tracks):
            y0 = track_top + i * self.TRACK_HEIGHT
            y1 = y0 + self.TRACK_HEIGHT
            mid = (y0 + y1) // 2
            band_color = th.blend_color(tr["color"], 0.30)
            mark_color = th.blend_color(tr["color"], 0.85)
            track_selected = self._is_highlighted("track", tr["id"])
            band_outline = self.SELECTION_COLOR if track_selected else "#000000"
            c.create_rectangle(0, y0, w, y1, fill=band_color, outline=band_outline,
                               width=2 if track_selected else 1)
            self._track_band_regions[tr["id"]] = (y0, y1)

            label_tag = f"tracklabel_{tr['id']}"
            c.create_text(6, mid, text=tr["name"], fill="#ffffff", anchor="w",
                          font=("TkDefaultFont", 8, "bold"), tags=(label_tag,))
            self._track_label_regions[tr["id"]] = c.bbox(label_tag)

            track_pool = [m for m in self.marks if m.get("track_id") == tr["id"]]
            _visible_track, track_lanes, track_lane_count = self._marks_with_lanes(track_pool, w)
            lane_h = self.TRACK_HEIGHT / track_lane_count

            for m in self.marks:
                if m.get("track_id") != tr["id"]:
                    continue
                if m["type"] == "point":
                    if not (self.view_start <= m["start"] <= self.view_end):
                        continue
                elif m["end"] < self.view_start or m["start"] > self.view_end:
                    continue
                mark_selected = self._is_highlighted("mark", m["id"])
                this_mark_color = self.SELECTION_COLOR if mark_selected else mark_color
                tag = f"mark_{m['id']}"
                text_tag = f"marktext_{m['id']}"
                x1 = x_of(max(m["start"], self.view_start))
                lane = track_lanes[m["id"]]
                sub_y0, sub_y1 = y0 + lane * lane_h, y0 + (lane + 1) * lane_h
                sub_mid = (sub_y0 + sub_y1) / 2
                if m["type"] == "range":
                    x2 = x_of(min(m["end"], self.view_end))
                    outline = self.SELECTION_COLOR if mark_selected else ""
                    pad = min(4, lane_h / 4)
                    c.create_rectangle(x1, sub_y0 + pad, x2, sub_y1 - pad, fill=this_mark_color, outline=outline,
                                       width=2 if mark_selected else 1, tags=(tag,))
                    ts_text = f"{th.format_time_ms(m['start'])} - {th.format_time_ms(m['end'])}"
                else:
                    c.create_line(x1, sub_y0, x1, sub_y1, fill=this_mark_color, width=3 if mark_selected else 2,
                                  tags=(tag,))
                    ts_text = th.format_time_ms(m["start"])
                label = (th.strip_adjustments(m["label"] or "") or ts_text).replace("\n", " / ")
                c.create_text(x1 + 3, sub_mid, text=label, fill="#ffffff", anchor="w",
                              font=("TkDefaultFont", 7), tags=(tag, text_tag))
                self._mark_hit_regions[m["id"]] = c.bbox(text_tag)

        self._render_status_row(w, layout)

    def _render_status_row(self, w, layout):
        """One row right under the waveform: playback / view / analysis
        status on the left, the stem color key on the right, and it's the
        drop target for creating a new track (hint shown while dragging a
        mark, or while there are no tracks yet)."""
        c = self.canvas
        y0, y1 = layout["row_top"], layout["track_top"]
        mid = (y0 + y1) // 2
        font = ("TkDefaultFont", 8)
        c.create_rectangle(0, y0, w, y1, fill=TB_BG, outline="")
        c.create_line(0, y0, w, y0, fill="#000000")

        status = self._status_text()
        self._last_status_drawn = status
        if status:
            c.create_text(6, mid, text=status, fill=TB_DIM, anchor="w", font=font, tags=("status_text",))

        right = w - 6
        self._legend_hits = []    # (x0, x1, kind): click a chip or its name to change that color
        if self.regions:
            for kind in reversed(("vocal", "novocal", "mixed", "silent")):
                tid = c.create_text(right, mid, text=STEM_LABELS[kind], fill=TB_DIM, anchor="e", font=font,
                                    tags=("legend", f"legend_{kind}"))
                bbox = c.bbox(tid) or (right - 30, 0, right, 0)
                x_chip = bbox[0] - 4
                c.create_rectangle(x_chip - 9, mid - 4, x_chip - 1, mid + 4, fill=self.region_colors[kind],
                                   outline="", tags=("legend", f"legend_{kind}"))
                self._legend_hits.append((x_chip - 10, right + 2, kind))
                right = x_chip - 14

        dragging_mark = bool(self._move_drag) and self._move_drag.get("edge") is None
        file_hover = getattr(self, "_drop_hover", False)
        if file_hover:
            c.create_rectangle(1, y0 + 1, w - 1, y1 - 1, outline=TB_ACCENT, width=2, dash=(4, 2))
            c.create_text(w // 2, mid, text="drop to import as a new timing track", fill=TB_ACCENT, font=font,
                          tags=("drop_hint",))
        elif dragging_mark or not self.tracks:
            c.create_text(w // 2, mid, text="drop a mark (or a lyrics / labels file) here for a new track",
                          fill=TB_ACCENT if dragging_mark else "#6a6a6a", font=font, tags=("drop_hint",))

    def _render_drag_preview(self, w, layout):
        if not self._move_drag or self._move_drag.get("edge") is not None:
            return
        zone, target = self._move_drag.get("preview_zone", (None, None))
        if zone is None:
            return
        orig_track_id = self._move_drag.get("orig_track_id")
        orig_zone = ("work", None) if orig_track_id is None else ("track", orig_track_id)
        if (zone, target) == orig_zone:
            return
        c = self.canvas
        if zone == "work":
            y0, y1 = 0, layout["work_height"]
        elif zone == "track":
            idx = next((i for i, t in enumerate(self.tracks) if t["id"] == target), None)
            if idx is None:
                return
            y0 = layout["track_top"] + idx * self.TRACK_HEIGHT
            y1 = y0 + self.TRACK_HEIGHT
        else:
            y0, y1 = layout["row_top"], layout["track_top"]
        c.create_rectangle(1, y0 + 1, w - 1, y1 - 1, outline=self.SELECTION_COLOR, width=2, dash=(4, 2))

    def _render_cursor(self, x_of, layout):
        """The @cursor -- always shown. It is the playback position: solid
        while playing, dashed otherwise, with an "@" tag in the status row
        (the position the cards' @ buttons and Split use)."""
        if self.audio_duration is None:
            return
        t = self.cursor_position() or 0.0
        if not (self.view_start <= t <= self.view_end):
            return
        x = x_of(t)
        c = self.canvas
        if self._play_state == "playing":
            c.create_line(x, 0, x, layout["total_h"], fill=CURSOR_PLAY_COLOR, width=2, tags=("cursor_line",))
        else:
            c.create_line(x, 0, x, layout["total_h"], fill=CURSOR_COLOR, dash=(2, 3), tags=("cursor_line",))
        y0, y1 = layout["row_top"], layout["track_top"]
        tx = max(8, min(self._canvas_size()[0] - 8, x))   # keep the tag on screen at 0:00 / the end
        c.create_rectangle(tx - 7, y0 + 3, tx + 7, y1 - 3, fill=CURSOR_COLOR, outline="", tags=("cursor_at",))
        c.create_text(tx, (y0 + y1) // 2, text="@", fill="#1e1e1e", font=("TkDefaultFont", 8, "bold"),
                      tags=("cursor_at",))

    def _render_playhead(self, x_of, layout):
        """(Merged into the @cursor -- see _render_cursor.)"""
        return

    def _render_time_readout(self, w):
        text = xy = None
        if self._move_drag and self._move_drag.get("last_xy"):
            xy = self._move_drag["last_xy"]
            mark = self._move_drag["mark"]
            edge = self._move_drag.get("edge")
            if edge == "start":
                text = f"start {th.format_time_ms(mark['start'])}"
            elif edge == "end":
                text = f"end {th.format_time_ms(mark['end'])}"
            elif mark["type"] == "point":
                text = th.format_time_ms(mark["start"])
            else:
                text = f"{th.format_time_ms(mark['start'])} - {th.format_time_ms(mark['end'])}"
        elif self._press_info and self._press_info.get("dragging") and self._press_info.get("last_xy") \
                and self._preview_range:
            xy = self._press_info["last_xy"]
            ps, pe = self._preview_range
            text = f"{th.format_time_ms(ps)} - {th.format_time_ms(pe)}"
        if text is None:
            return
        c = self.canvas
        x, y = xy
        tx, ty = min(w - 10, x + 12), max(2, y - 16)
        box_w = max(36, len(text) * 6 + 8)
        c.create_rectangle(tx - 4, ty - 2, tx + box_w, ty + 12, fill="#000000", outline=self.SELECTION_COLOR)
        c.create_text(tx, ty, text=text, fill=self.SELECTION_COLOR, anchor="nw", font=("TkDefaultFont", 7, "bold"))


# ---------------------------------------------------------------------------
# Plugin entry point
# ---------------------------------------------------------------------------

_BACKED_UP = set()      # sidecars already backed up in this run of the app


def backup_sidecar_once(media_path):
    """Preference "Back up sidecar files": the first time this run opens a
    file (the session's files at startup), copy its "-tracked.json" to a
    timestamped .bak (only the newest backup is kept)."""
    if not get_preference("backup_sidecars", False):
        return None
    cache = th.cache_path(media_path)
    if cache in _BACKED_UP:
        return None
    _BACKED_UP.add(cache)
    dest = th.backup_sidecar(cache)
    if dest:
        debug(2, f"{{blue}}Backed up {Path(cache).name} -> {Path(dest).name}")
    return dest


def onload(filepath: str, canvas=None, text=None, tab=None):
    p = Path(filepath)
    if p.suffix.lower() not in AUDIO_EXTS:
        return False
    if canvas is not None:
        backup_sidecar_once(str(p.resolve()))

    descr = (
        f"{{cyan}}[waveform_tab]\n"
        f"{{blue}}Audio: {{cyan}}{p.name}\n"
        f"{{blue}}Path:  {p.resolve()}\n"
    )
    descr += _metadata_text(str(p.resolve()))

    backend = th.waveform_backend_for(str(p.resolve()))
    if backend:
        descr += f"\n{{blue}}Waveform decoder: {{cyan}}{backend}\n"
        if backend == "miniaudio":
            descr += ("{yellow}  Note: miniaudio decodes the whole file for each deep-zoom redraw, so "
                      "zooming in past the overview will be slower (ffmpeg or soundfile avoid this).\n")
        elif "miniaudio" in backend:
            descr += ("{yellow}  Note: if soundfile can't read this file, miniaudio is used instead and "
                      "deep-zoom redraws will be slower.\n")
    else:
        descr += f"\n{{red}}Waveform decoder: none available \u2013 {_decoder_hint(filepath)}\n"
    engine_name = "sounddevice (trackED's own)" if th.ACTIVE_ENGINE == "sounddevice" else "ffplay (Sequence Editor's original)"
    descr += f"{{blue}}Playback engine: {{cyan}}{engine_name}\n"

    missing = deps.missing()
    if missing:
        descr += ("\n{yellow}Missing dependencies: " + ", ".join(d["key"] for d in missing)
                  + ".\n{yellow}Use the \u26a0 Install button in the upper right corner to install them.\n")
    else:
        descr += "\n{green}All optional packages are present.\n"
    whisper = aa.whisper_backends()
    if whisper:
        descr += (f"{{blue}}Transcription: {{cyan}}{', '.join(whisper)}  (auto model: "
                  f"{aa.default_whisper_model()}, {aa.available_ram_gb():.1f} GB free)\n")

    descr += (
        "\n{blue}Mouse: {cyan}click{blue}=move the @cursor  {cyan}double-click{blue} or {cyan}M{blue}=new point mark  "
        "{cyan}drag{blue}=new range\n"
        "{blue}      {cyan}shift+click{blue}=range from the @cursor (or a just-made point) to here\n"
        "{blue}Keys:  {cyan}M{blue}=point mark at the @cursor  {cyan}Delete{blue}=delete selection  "
        "{cyan}Ctrl+Z/Y{blue}=undo/redo\n"
        "{blue}      type a time in the position box + Enter to move the @cursor; drag the slider to scroll\n"
        "{blue}Lyrics: drag a .txt/.lrc/.srt/labels file onto the row under the waveform (or right-click it)"
        " for a new track;\n{blue}      a card's {cyan}Split \u25be{blue} splits at the cursor, a selected phrase, "
        "or into words (timed by syllables)\n"
        "{blue}      {cyan}drag a mark{blue}=move/resize  {cyan}drag into a track band{blue}=assign it\n"
        "{blue}      in a track: {cyan}Ctrl+click{blue}=add/remove a mark from the selection  "
        "{cyan}Shift+click{blue}=select a run;\n{blue}      {cyan}Ctrl+C/X/V{blue}=copy/cut/paste marks "
        "(paste goes into the selected track, same times); right-click for Move/Copy to Track\n"
        "{blue}      {cyan}double-click{blue}=edit label  {cyan}right-click{blue}=mark/track menu "
        "(split / merge / transcribe)\n"
        "{blue}      {cyan}Ctrl+click{blue}=move the @cursor (= playhead)  {cyan}Shift+Play{blue}=loop\n"
        "{blue}      {cyan}\u25c0\u25c0 / \u25b6\u25b6{blue}: click=5 s, Shift+click=stem region edge, "
        "Ctrl+click=start/end of the audio\n"
        "{blue}      {cyan}select a track or one of its marks{blue}=edit its marks here in the text panel\n"
        "{blue}      cards: {cyan}Voice \u25be{blue}=assign voices (or right-click a mark on the waveform); "
        "hover a word for its syllables/time,\n"
        "{blue}      {cyan}right-click a word{blue} or {cyan}Alt+\u2191/\u2193{blue} (syllables), "
        "{cyan}Alt+\u2192/\u2190{blue} (time) to adjust: writes {cyan}word {+1}{blue} / "
        "{cyan}word {-0.1s}{blue} into the text\n"
        "{blue}      card keys: {cyan}Enter{blue}=next card  {cyan}Ctrl+Enter{blue}=split at the text cursor  "
        "{cyan}Backspace{blue} at the start / {cyan}Delete{blue} at the end=merge  {cyan}Ctrl+Space{blue}=play/pause  "
        "{cyan}Ctrl+[{blue} / {cyan}Ctrl+]{blue}=Start/End to @cursor  {cyan}Tab{blue}=same field, next card (wraps)  {cyan}Ctrl+Home/End{blue}=first/last card\n"
        "{blue}Keys:  {cyan}Up/Down{blue}=move selection between tracks  {cyan}Left/Right{blue}=nudge by one grid step\n"
        "{blue}       {cyan}Tab/Shift+Tab{blue}=select next/prev mark  {cyan}Delete{blue}=delete selection\n"
        "{blue}       {cyan}Home/End{blue}=first/last mark of the track  (Help > Keyboard Shortcuts lists them all)\n"
        "{blue}       {cyan}Ctrl+Z/Ctrl+Y{blue}=undo/redo marks (while the waveform has focus)\n"
        "{blue}       {cyan}wheel{blue}=zoom\n"
        "{blue}Export Timing (xLights/LRC/Audacity): right-click a track's label.\n"
    )

    if canvas is not None:
        canvas.delete("all")
        for seq in canvas.bind():
            canvas.unbind(seq)
        # Stop/release any controller a previous onload() call on this same
        # canvas left running, before replacing it.
        old = getattr(canvas, "_waveform_controller", None)
        if old is not None:
            try:
                old.stop_and_release()
            except Exception:
                pass
        # Keep a reference so it isn't garbage-collected.
        controller = WaveformController(canvas, text, str(p.resolve()), tab=tab)
        canvas._waveform_controller = controller
        # Don't call tab.paned.sashpos() here: this runs inside EditorTab's
        # load_file(), before the tab is mapped, and editor_tab's own
        # _restore_sash() runs ~40ms later and overwrites it with the saved
        # (or 60px default) position -- which is why the waveform canvas
        # ended up squeezed to nothing under its toolbars. Instead, hand
        # editor_tab size hints it applies when it restores the sash.
        if tab is not None:
            tab.min_sash = controller.min_panel_height
            tab.preferred_sash = controller.preferred_panel_height
            # The text panel shows info/marks for an audio file; never let
            # File > Save write that text over the audio.
            tab.protect_file = True
            # Undo/redo in this tab means timing marks, wherever the focus
            # is (Edit menu, text panel, card fields, waveform).
            tab.undo_hook = controller.undo_marks
            tab.redo_hook = controller.redo_marks
            tab.save_hook = controller.save_marks_now
            tab.before_close_hook = controller.before_close
            tab.teardown_hook = controller.teardown
            _bind_undo_keys(tab, text)
        controller.set_info_text(descr)

    if text is not None:
        text.configure(state="normal")
        text.delete("1.0", "end")
        insert_styled_text(text, descr)

    return True

# eof
