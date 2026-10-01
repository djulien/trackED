"""Utility functions and generic helpers."""

from __future__ import annotations

import json
import os
import re
import platform
import sys
import time
import re
import tkinter as tk
from pathlib import Path
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple
#NO-RECURSION: from logview_tab import debug


# These will be set / overridden by main.py constants when imported
APP_NAME = "trackED"
VERSION = "1.0.0"
clean_name = re.sub(r'[^\x20-\x7E]', '_', APP_NAME).lower()

# Config lives in the user's home directory
CONFIG_DIR = Path.home() / f".{clean_name}"
SESSION_FILE = CONFIG_DIR / "session.json"
MAX_RECENT = 10

# Factory default for the persistent "debug_level" preference (0 = off,
# 1 = high-level only ... 99 = everything). See get_default_debug_level().
DEFAULT_DEBUG_LEVEL = 10

# Factory default for the "autosave_seconds" preference (0 = off).
DEFAULT_AUTOSAVE_SECONDS = 10

# Stem regions shorter than this (seconds) are merged into their neighbors.
DEFAULT_STEM_MIN_SECONDS = 1.0

# Default sash position (pixels from top) when no saved value exists
DEFAULT_SASH_POS = 60  #small default height


def ensure_config_dir() -> None:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)


def _default_session() -> Dict[str, Any]:
    return {
        "recent": [],
        "open_files": [],
        "active_index": 0,
        "sash_positions": {},
        "cursor_positions": {},   # path -> {"index": "line.col", "yview": float}
        "preferences": {
            "max_recent": 10,
            "debug_level": DEFAULT_DEBUG_LEVEL,
            "autosave_seconds": DEFAULT_AUTOSAVE_SECONDS,
            "stem_min_seconds": DEFAULT_STEM_MIN_SECONDS,
#            "debug_wrap": False,
#            "debug_filter": "",
        },
    }


def get_preference(key: str, default: Any = None) -> Any:
    data = load_session_data()
    prefs = data.get("preferences", {})
    return prefs.get(key, default)


def set_preference(key: str, value: Any) -> None:
    data = load_session_data()
    data.setdefault("preferences", {})[key] = value
    save_session_data(data)


def get_default_debug_level() -> int:
    """Debug level used when the command line doesn't give one (the
    persistent "debug_level" preference; DEFAULT_DEBUG_LEVEL if unset)."""
    try:
        return max(0, min(99, int(get_preference("debug_level", DEFAULT_DEBUG_LEVEL))))
    except (TypeError, ValueError):
        return DEFAULT_DEBUG_LEVEL


def set_default_debug_level(level: Optional[int]) -> int:
    """Store a new default debug level; None resets it to the factory
    DEFAULT_DEBUG_LEVEL. Returns the stored value."""
    value = DEFAULT_DEBUG_LEVEL if level is None else max(0, min(99, int(level)))
    set_preference("debug_level", value)
    return value


def get_autosave_seconds() -> int:
    """Auto-save interval in seconds from Preferences (0 = off)."""
    try:
        return max(0, min(3600, int(get_preference("autosave_seconds", DEFAULT_AUTOSAVE_SECONDS))))
    except (TypeError, ValueError):
        return DEFAULT_AUTOSAVE_SECONDS


def get_stem_min_seconds() -> float:
    """Shortest stem region kept (Preferences); shorter ones are merged."""
    try:
        return max(0.0, min(30.0, float(get_preference("stem_min_seconds", DEFAULT_STEM_MIN_SECONDS))))
    except (TypeError, ValueError):
        return DEFAULT_STEM_MIN_SECONDS


DEFAULT_EDGE_LEAD_IN = 0.15


def get_edge_lead_in() -> float:
    """Seconds a card's Start is put before a detected rising edge (the
    sound usually starts a little before the edge's foot). Preferences."""
    try:
        return max(0.0, min(2.0, float(get_preference("edge_lead_in", DEFAULT_EDGE_LEAD_IN))))
    except (TypeError, ValueError):
        return DEFAULT_EDGE_LEAD_IN


def get_max_recent() -> int:
    """Read MAX_RECENT from Preferences; default 10."""
    try:
        val = int(get_preference("max_recent", 10))
        return max(1, min(val, 100))   # sane bounds
    except (TypeError, ValueError):
        return 10

# ---------- text styling ----------------

import re
import tkinter as tk
from typing import List, Optional, Tuple

# Display tags: {red}, {bold}, {reset}, ...
_STYLE_TAG_RE = re.compile(r"\{([a-zA-Z]+)\}")
# Leading debug/log timestamp: [HH:MM:SS.mmm]
_TIMESTAMP_RE = re.compile(r"^(\[[0-9:.]+])(\s*)")

_LOG_COLORS = {
    "red": "#e74c3c",
    "green": "#2ecc71",
    "blue": "#3498db",
    "yellow": "#f1c40f",
    "orange": "#e67e22",
    "cyan": "#1abc9c",
    "magenta": "#9b59b6",
    "pink": "#9b59b6",  #easier to spell :P
    "white": "#ecf0f1",
    "gray": "#95a5a6",
    "grey": "#95a5a6",
    "black": "#2c3e50",
}

_FONT_STYLE_TAGS = frozenset({"bold", "italic", "underline"})


def ensure_style_tags(text: tk.Text) -> None:
    """Configure Tk tags once per Text widget."""
    if getattr(text, "_style_tags_ready", False):
        return
    base = text.cget("font")
    # Derive bold/italic from current font if possible
    try:
        family, size = tk.font.nametofont(base).actual("family"), tk.font.nametofont(base).actual("size")
    except Exception:
        try:
            # font might be a tuple string
            import tkinter.font as tkfont
            f = tkfont.Font(font=base)
            family, size = f.actual("family"), f.actual("size")
        except Exception:
            family, size = "TkFixedFont", 10

    import tkinter.font as tkfont
    for name, color in _LOG_COLORS.items():
        text.tag_configure(f"style_fg_{name}", foreground=color)
    text.tag_configure("style_bold", font=tkfont.Font(family=family, size=size, weight="bold"))
    text.tag_configure("style_italic", font=tkfont.Font(family=family, size=size, slant="italic"))
    text.tag_configure("style_underline", underline=True)
    # bold+italic combo used when both active
    text.tag_configure(
        "style_bold_italic",
        font=tkfont.Font(family=family, size=size, weight="bold", slant="italic"),
    )
    text._style_tags_ready = True


def _tags_for_state(color: Optional[str], bold: bool, italic: bool, underline: bool) -> Tuple[str, ...]:
    tags = []
    if color and color in _LOG_COLORS:
        tags.append(f"style_fg_{color}")
    if bold and italic:
        tags.append("style_bold_italic")
    elif bold:
        tags.append("style_bold")
    elif italic:
        tags.append("style_italic")
    if underline:
        tags.append("style_underline")
    return tuple(tags)


def parse_styled_line(line: str) -> List[Tuple[str, Tuple[str, ...]]]:
    """
    Split one line into (visible_text, tk_tag_tuple) segments.
    Supports {color}, {bold}, {italic}, {underline}, {reset}.
    If a color tag appears immediately after a leading [timestamp], that color
    also applies to the timestamp.
    """
    # Detect "timestamp + optional space + {color}" for whole-line-from-start color
    early_color: Optional[str] = None
    m = _TIMESTAMP_RE.match(line)
    if m:
        rest = line[m.end():]
        m2 = _STYLE_TAG_RE.match(rest)
        if m2:
            name = m2.group(1).lower()
            if name in _LOG_COLORS:
                early_color = name

    color: Optional[str] = early_color
    bold = italic = underline = False
    segments: List[Tuple[str, Tuple[str, ...]]] = []
    pos = 0

    for m in _STYLE_TAG_RE.finditer(line):
        if m.start() > pos:
            piece = line[pos:m.start()]
            if piece:
                segments.append((piece, _tags_for_state(color, bold, italic, underline)))
        name = m.group(1).lower()
        if name == "reset":
            color, bold, italic, underline = None, False, False, False
        elif name in _LOG_COLORS:
            color = name
        elif name == "bold":
            bold = True
        elif name == "italic":
            italic = True
        elif name == "underline":
            underline = True
        # unknown tags: ignored (and not shown)
        pos = m.end()

    if pos < len(line):
        piece = line[pos:]
        if piece:
            segments.append((piece, _tags_for_state(color, bold, italic, underline)))

    # If early_color was set, re-tag the timestamp prefix with that color
    if early_color and segments:
        ts = _TIMESTAMP_RE.match(line)
        if ts:
            ts_text = ts.group(1) + ts.group(2)
            # Rebuild: first segment(s) that display ts_text should include color
            # Easier approach: prepend handling by painting timestamp in early_color
            rebuilt: List[Tuple[str, Tuple[str, ...]]] = []
            remaining_ts = ts_text
            for piece, tags in segments:
                if remaining_ts and piece.startswith(remaining_ts):
                    rebuilt.append((remaining_ts, _tags_for_state(early_color, False, False, False)))
                    rest = piece[len(remaining_ts):]
                    if rest:
                        rebuilt.append((rest, tags))
                    remaining_ts = ""
                elif remaining_ts and remaining_ts.startswith(piece):
                    rebuilt.append((piece, _tags_for_state(early_color, False, False, False)))
                    remaining_ts = remaining_ts[len(piece):]
                else:
                    if remaining_ts:
                        rebuilt.append((remaining_ts, _tags_for_state(early_color, False, False, False)))
                        remaining_ts = ""
                    rebuilt.append((piece, tags))
            if remaining_ts:
                rebuilt.insert(0, (remaining_ts, _tags_for_state(early_color, False, False, False)))
            segments = rebuilt

    return segments if segments else [("", ())]


def insert_styled_text(text: tk.Text, content: str, index: str = "end") -> None:
    """
    Insert content into a Text widget, honoring {color}/{bold}/…/{reset} tags.
    Works for full multi-line strings (each line styled independently).
    """
    ensure_style_tags(text)
    lines = content.splitlines(keepends=True)
    if not lines and content:
        lines = [content]
    for raw in lines:
        if raw.endswith("\n"):
            line, nl = raw[:-1], "\n"
        else:
            line, nl = raw, ""
        for piece, tags in parse_styled_line(line):
            if not piece:
                continue
            if tags:
                text.insert(index, piece, tags)
            else:
                text.insert(index, piece)
        if nl:
            text.insert(index, nl)


def strip_style_tags(content: str) -> str:
    """Visible plain text with {tags} removed (e.g. for save-to-disk)."""
    return _STYLE_TAG_RE.sub("", content)


# ---------- recent files (now use get_max_recent) ----------

def load_session_data() -> Dict[str, Any]:
    ensure_config_dir()
    if not SESSION_FILE.exists():
        return _default_session()
    try:
        data = json.loads(SESSION_FILE.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            return _default_session()
        # ensure required keys exist
        base = _default_session()
        base.update(data)
        return base
    except Exception:
        return _default_session()


def save_session_data(data: Dict[str, Any]) -> None:
    ensure_config_dir()
    SESSION_FILE.write_text(json.dumps(data, indent=2), encoding="utf-8")


# ---------- convenience wrappers ----------

def load_recent() -> List[str]:
    data = load_session_data()
    max_r = get_max_recent()
    return [p for p in data.get("recent", []) if isinstance(p, str) and Path(p).exists()][:max_r]


def save_recent(paths: List[str]) -> None:
    data = load_session_data()
    # Keep unique, most-recent first
    max_r = get_max_recent()
    seen = set()
    unique = []
    for p in paths:
        if p not in seen and Path(p).exists():
            seen.add(p)
            unique.append(p)
    data["recent"] = unique[:max_r]
    save_session_data(data)


def add_recent(path: str) -> List[str]:
    recent = load_recent()
    if path in recent:
        recent.remove(path)
    recent.insert(0, path)
    save_recent(recent)
    return recent


def get_sash_pos(filepath: Optional[str], default: Optional[int] = None) -> int:
    """Saved sash position for this file, else `default` (a plugin's
    preferred panel height, if it gave one), else DEFAULT_SASH_POS."""
    if default is None:
        default = DEFAULT_SASH_POS
    if not filepath:
        return int(default)
    key = str(Path(filepath).resolve())
    return int(load_session_data().get("sash_positions", {}).get(key, default))


def set_sash_pos(filepath: Optional[str], pos: int) -> None:
    if not filepath:
        return
    key = str(Path(filepath).resolve())
    data = load_session_data()
    data.setdefault("sash_positions", {})[key] = max(30, int(pos))
    save_session_data(data)


def get_cursor_pos(filepath: Optional[str]) -> Dict[str, Any]:
    if not filepath:
        return {"index": "1.0", "yview": 0.0}
    key = str(Path(filepath).resolve())
    return load_session_data().get("cursor_positions", {}).get(
        key, {"index": "1.0", "yview": 0.0}
    )


def set_cursor_pos(filepath: Optional[str], index: str, yview: float) -> None:
    if not filepath:
        return
    key = str(Path(filepath).resolve())
    data = load_session_data()
    data.setdefault("cursor_positions", {})[key] = {
        "index": index,
        "yview": float(yview),
    }
    save_session_data(data)


def abbreviated_name(path: Optional[str], max_len: int = 24) -> str:
    """Return a short display name for a tab label."""
    if not path:
        return "Untitled"
    name = Path(path).name
    if len(name) <= max_len:
        return name
    # keep extension if possible
    stem, suffix = Path(name).stem, Path(name).suffix
    keep = max_len - len(suffix) - 3
    if keep < 4:
        return name[: max_len - 3] + "..."
    return stem[:keep] + "..." + suffix


def about_text() -> str:
    return (
        f"{APP_NAME}\n"
        f"Version {VERSION}\n\n"
        "A lightweight cross-platform text editor\n"
        "written in pure Python + Tkinter.\n\n"
        f"Python {sys.version.split()[0]}  |  {platform.system()} {platform.release()}"
    )


def documentation_url() -> str:
    # Placeholder – replace with real docs when available
    return "https://github.com/example/simple-multi-tab-editor#readme"


def available_memory_str() -> str:
    """Return a short human-readable available-memory string (stdlib only)."""
    try:
        if sys.platform == "win32":
            import ctypes
            class MEMORYSTATUSEX(ctypes.Structure):
                _fields_ = [
                    ("dwLength", ctypes.c_ulong),
                    ("dwMemoryLoad", ctypes.c_ulong),
                    ("ullTotalPhys", ctypes.c_ulonglong),
                    ("ullAvailPhys", ctypes.c_ulonglong),
                    ("ullTotalPageFile", ctypes.c_ulonglong),
                    ("ullAvailPageFile", ctypes.c_ulonglong),
                    ("ullTotalVirtual", ctypes.c_ulonglong),
                    ("ullAvailVirtual", ctypes.c_ulonglong),
                    ("ullAvailExtendedVirtual", ctypes.c_ulonglong),
                ]
            stat = MEMORYSTATUSEX()
            stat.dwLength = ctypes.sizeof(MEMORYSTATUSEX)
            ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(stat))
            avail = stat.ullAvailPhys / (1024 * 1024)
            total = stat.ullTotalPhys / (1024 * 1024)
            return f"{avail:.0f} MB free / {total:.0f} MB total"
        else:
            # Linux / most Unix
            info = {}
            with open("/proc/meminfo", encoding="utf-8") as f:
                for line in f:
                    parts = line.split()
                    if len(parts) >= 2:
                        info[parts[0].rstrip(":")] = int(parts[1])  # kB
            avail = info.get("MemAvailable", info.get("MemFree", 0)) / 1024
            total = info.get("MemTotal", 0) / 1024
            return f"{avail:.0f} MB free / {total:.0f} MB total"
    except Exception as e:
        return f"(unavailable: {e})"


def is_probably_text_file(path: str, sample_size: int = 8192) -> bool:
    """Heuristic: no NUL in the first chunk and mostly printable/UTF-8."""
    try:
        with open(path, "rb") as f:
            chunk = f.read(sample_size)
        if not chunk:
            return True
        if b"\x00" in chunk:
            return False
        # try utf-8
        try:
            chunk.decode("utf-8")
            return True
        except UnicodeDecodeError:
            pass
        # latin-1 always decodes; check printable ratio
        text_chars = bytes(range(32, 127)) + b"\n\r\t\b\f"
        nontext = sum(1 for b in chunk if b not in text_chars)
        return (nontext / len(chunk)) < 0.30
    except Exception:
        return False


def file_meta_summary(path: str) -> str:
    p = Path(path)
    try:
        st = p.stat()
        size = st.st_size
        mtime = datetime.fromtimestamp(st.st_mtime).strftime("%Y-%m-%d %H:%M:%S")
        return (
            "{{red}}[unclaimed]\n"
            f"{{blue}}File: {{cyan}}{p.name}\n"
            f"{{blue}}Path: {p.resolve()}\n"
            f"{{blue}}Size: {{cyan}}{size:,} bytes\n"
            f"{{blue}}Last modified: {{cyan}}{mtime}\n"
        )
    except Exception as exc:
        return f"{{blue}}File: {{cyan}}{path}\n{{red}}error reading metadata: {exc}\n"


_tab_plugins_cache = None  # list of modules, or None = not loaded yet

def clear_tab_plugins_cache() -> None:
    global _tab_plugins_cache, _FILE_TYPES_CACHE
    _tab_plugins_cache = None
    _FILE_TYPES_CACHE = None

def discover_tab_plugins() -> list:
    """
    Find all *_tab.py modules beside the app (and cwd) that define onload().
    Results are cached for the rest of the process (plugins are assumed fixed).
    """
    global _tab_plugins_cache
    if _tab_plugins_cache is not None:
        return _tab_plugins_cache

    import importlib.util

    search_dirs = []
    # directory containing main.py / this package
    try:
        app_dir = Path(__file__).resolve().parent
        search_dirs.append(app_dir)
    except Exception:
        pass
    cwd = Path.cwd()
    if cwd not in search_dirs:
        search_dirs.append(cwd)

    modules = []
    seen = set()
    for d in search_dirs:
        for py in sorted(d.glob("*_tab.py")):
            key = str(py.resolve())
            #debug(9, key)
            #print("key " + key)
            if key in seen:
                continue
            # skip our own editor_tab / debug_tab implementation files if they
            # don't define a plugin-style onload (they will simply be ignored)
            seen.add(key)
            try:
                spec = importlib.util.spec_from_file_location(py.stem, py)
                if spec is None or spec.loader is None:
                    debug(5, f"{{red}}key '{key}' no spec")
                    continue
                mod = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(mod)
                if callable(getattr(mod, "onload", None)):
                    #debug(9, type(mod))
                    debug(5, f"{{green}}mod '{mod.__name__}' callable")
                    modules.append(mod)
                else:
                    debug(5, f"{{red}}mod '{mod.__name__}' !onload")
            except Exception as exc:
                debug(5, f"{{red}}key '{key}' !callable: {exc}")
                import traceback
                traceback.print_exc()
                continue
    debug(5, f"{{cyan}}found {len(modules)} tab extensions")
    _tab_plugins_cache = sorted(modules, key=lambda m: m.__name__)
    return _tab_plugins_cache


_FILE_TYPES_CACHE: Optional[list] = None


def plugin_file_types() -> list:
    """File-dialog entries the *_tab.py plugins declare, in plugin order:
    each plugin may define FILE_TYPES = [("Label", "*.ext *.ext2"), ...]
    (or a file_types() function returning that list). Collected once per
    session (plugins don't change while the app runs); cleared together
    with the plugin list by clear_tab_plugins_cache()."""
    global _FILE_TYPES_CACHE
    if _FILE_TYPES_CACHE is not None:
        return list(_FILE_TYPES_CACHE)
    out = []
    for mod in discover_tab_plugins():
        try:
            entries = getattr(mod, "FILE_TYPES", None)
            if callable(getattr(mod, "file_types", None)):
                entries = mod.file_types()
            for label, patterns in entries or []:
                if label and patterns:
                    out.append((str(label), str(patterns)))
        except Exception as exc:
            debug(5, f"{{red}}{mod.__name__} file types: {exc}")
    _FILE_TYPES_CACHE = out
    return list(out)


def run_onload_plugins(filepath: str, canvas=None, text=None, tab=None) -> bool:
    """
    Call onload(...) on every *_tab.py plugin.
    Plugins may set text/canvas contents directly.
    Return True if a plugin claimed the file (truthy onload result).
    """
    import inspect

    candidates = discover_tab_plugins()
    debug(5, f"{{blue}}onload: {len(candidates)} candidate(s)")
    for mod in candidates:
        try:
            fn = getattr(mod, "onload", None)
            if not callable(fn):
                debug(5, f"{{blue}}{mod.__name__} onload !callable")
                continue
            sig = inspect.signature(fn)
            kwargs = {}
            if "canvas" in sig.parameters:
                kwargs["canvas"] = canvas
            if "text" in sig.parameters:
                kwargs["text"] = text
            if "tab" in sig.parameters:
                kwargs["tab"] = tab
            result = fn(filepath, **kwargs) if kwargs else fn(filepath)
            if result:
                debug(5, f"{{green}}{mod.__name__} onload CLAIMED")
                return True
        except Exception as exc:
            debug(5, "{{red}}", mod.__name__, "exc:", exc)
            import traceback
            traceback.print_exc()
            continue
    debug(5, f"{{yellow}}{mod.__name__} onload !claimed")
    return False


def OLD_run_onload_plugins(filepath: str, canvas=None, tab=None):
    """
    Call onload(filepath, canvas=..., tab=...) on every *_tab.py plugin.
    Return the first non-false result (string to show in the text area),
    or None if no plugin claims the file.

    Plugins may accept optional keyword args:
        onload(filepath)
        onload(filepath, canvas=None)
        onload(filepath, canvas=None, tab=None)
    """
    import inspect

    for mod in discover_tab_plugins():
        try:
            fn = getattr(mod, "onload", None)
            if not callable(fn):
                continue
            # Call with as many optional kwargs as the function accepts
            sig = inspect.signature(fn)
            kwargs = {}
            if "canvas" in sig.parameters:
                kwargs["canvas"] = canvas
            if "tab" in sig.parameters:
                kwargs["tab"] = tab
            debug(5, mod.__name__, kwargs, **kwargs)
            result = fn(filepath, **kwargs) if kwargs else fn(filepath)
            if result:
                return str(result)
        except Exception:
            continue
    return None

def OLD_run_onload_plugins(filepath: str) -> Optional[str]:
    """
    Call onload(filepath) on every *_tab.py plugin.
    Return the first non-false result (expected to be a string to display),
    or None if no plugin claims the file.
    """
    try:
        for mod in discover_tab_plugins():
            try:
                debug(5, "run " + mod.__name__)
                #print(mod.__name__)
                result = mod.onload(filepath)
                if result:
                    return str(result)
            except Exception as exc:
                debug(5, f"run {mod.__name__}? {exc}")
                #print(exc)
                continue
    except Exception as exc:
        debug(1, f"run {mod.__name__}: {exc}")
        #print("no run")
    return None

def find_create_tab_plugin(filepath: str):
    """
    Return (module, create_tab_fn) for the first *_tab.py that both
    claims this path and exposes create_tab().  Else None.
    """
    import inspect
    path = str(Path(filepath).resolve()) if filepath else ""
    for mod in discover_tab_plugins():
        create = getattr(mod, "create_tab", None)
        onload = getattr(mod, "onload", None)
        if not callable(create):
            continue
        # Prefer explicit handles() if present
        handles = getattr(mod, "handles", None)
        claimed = False
        if callable(handles):
            try:
                claimed = bool(handles(path))
            except Exception:
                claimed = False
        elif callable(onload):
            try:
                sig = inspect.signature(onload)
                kwargs = {}
                if "canvas" in sig.parameters:
                    kwargs["canvas"] = None
                if "tab" in sig.parameters:
                    kwargs["tab"] = None
                # Probe only: plugins should treat canvas=None as "claim test"
                result = onload(path, **kwargs) if kwargs else onload(path)
                claimed = bool(result)
            except Exception:
                claimed = False
        if claimed:
            return mod, create
    return None

#def debug(level: int, msg: str) -> None:
def debug(*args, **kwargs):
    """
    Thin wrapper so utils (and anyone) can log without importing debug_tab
    at module load time (avoids circular imports).
    TODO: make level optional?
    """
    kwargs['depth'] = kwargs.get('depth', 0) + 1  #show my caller
    #print(f"debug nest {kwargs['depth']}")
    try:
        from logview_tab import debug as _debug
        return _debug(*args, **kwargs)
    except Exception as exc:
        # debug system not loaded yet, or logging disabled – ignore
        print(f"debug wrapper: exc {exc}", file=sys.stderr) #show if can't log
        pass

#eof


# ---------------------------------------------------------------------------
# Buttons that do something else with Shift (or Ctrl) held: while the key
# is down, their icon turns amber, so it's visible which buttons change.
# ---------------------------------------------------------------------------

MOD_HINT_COLORS = {"shift": "#ffb000", "control": "#4fc3ff"}
_mod_buttons: list = []
_mod_listeners: list = []      # callables(set of held modifiers), e.g. a canvas showing a hint
_mod_state: set = set()
_mod_installed = False


def current_modifiers() -> set:
    return set(_mod_state)


def register_modifier_listener(fn, widget=None) -> None:
    """Call fn(set of held modifiers) whenever Shift/Ctrl go down or up
    (for controls that aren't buttons, e.g. the waveform canvas). Pass a
    widget so the key watch can be installed if no button did yet; a
    listener that raises (its widget is gone) is dropped."""
    _mod_listeners.append(fn)
    if widget is not None:
        _install_mod_watch(widget)


def _install_mod_watch(widget) -> None:
    global _mod_installed
    if _mod_installed:
        return
    try:
        root = widget.winfo_toplevel()
        for key, mod in (("Shift_L", "shift"), ("Shift_R", "shift"),
                         ("Control_L", "control"), ("Control_R", "control")):
            root.bind_all(f"<KeyPress-{key}>", lambda e, m=mod: _set_mod(m, True), add="+")
            root.bind_all(f"<KeyRelease-{key}>", lambda e, m=mod: _set_mod(m, False), add="+")
        root.bind_all("<FocusOut>", lambda e: _clear_mods(e), add="+")
        _mod_installed = True
    except Exception:
        pass


def register_modifier_button(button, mods=("shift",)) -> None:
    """Show button's alternate behavior while one of mods is held (the
    first held one in mods decides the color -- list them in the order the
    button checks them). The button's normal text color is taken from
    button._mod_normal_fg (set it when the color changes) or its fg."""
    try:
        if not hasattr(button, "_mod_normal_fg"):
            button._mod_normal_fg = button.cget("fg")
    except Exception:
        return
    _mod_buttons.append((button, tuple(mods)))
    _install_mod_watch(button)


def _clear_mods(event=None) -> None:
    # focus left the application (keys released elsewhere go unseen)
    try:
        if event is not None and event.widget.focus_get() is not None:
            return
    except Exception:
        pass
    if _mod_state:
        _mod_state.clear()
        _apply_mods()


def _set_mod(mod: str, down: bool) -> None:
    before = set(_mod_state)
    (_mod_state.add if down else _mod_state.discard)(mod)
    if _mod_state != before:
        _apply_mods()


def _apply_mods() -> None:
    alive = []
    for button, mods in _mod_buttons:
        try:
            active = [m for m in mods if m in _mod_state]
            fg = MOD_HINT_COLORS[active[0]] if active else getattr(button, "_mod_normal_fg", None)
            if fg:
                button.configure(fg=fg, activeforeground=fg)
            alive.append((button, mods))
        except Exception:
            pass               # destroyed: drop it
    _mod_buttons[:] = alive
    keep = []
    for fn in _mod_listeners:
        try:
            fn(set(_mod_state))
            keep.append(fn)
        except Exception:
            pass               # its widget is gone: drop it
    _mod_listeners[:] = keep


# ---------------------------------------------------------------------------
# Diagnostics: breadcrumbs of recent app steps (printed by tracked.py's
# stall watch when the GUI stops responding) and switches to turn suspect
# features off, for tracking down hangs:
#     TRACKED_DISABLE=prewarm,fit,spacers,linenumbers,see,slices,patch ./tracked.py
# ---------------------------------------------------------------------------

import collections as _collections
import os as _os
import threading as _threading
import time as _time

_crumbs = _collections.deque(maxlen=80)
_crumb_lock = _threading.Lock()
DISABLED_FEATURES = {f.strip().lower() for f in _os.environ.get("TRACKED_DISABLE", "").split(",") if f.strip()}


def feature_on(name: str) -> bool:
    """False if TRACKED_DISABLE lists this feature (diagnostics)."""
    return name.lower() not in DISABLED_FEATURES


def crumb(label: str) -> None:
    """Note an app step (cheap; a repeat of the last label just counts up)."""
    now = _time.monotonic()
    with _crumb_lock:
        if _crumbs and _crumbs[-1][1] == label:
            first, _label, count, _last = _crumbs[-1]
            _crumbs[-1] = (first, label, count + 1, now)
        else:
            _crumbs.append((now, label, 1, now))


def recent_crumbs() -> list:
    with _crumb_lock:
        return list(_crumbs)

