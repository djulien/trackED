"""
Generic log-file viewer tab + debug() helper.

- LogViewerTab: opens any log file, shows existing content, auto-refreshes
  when the file grows, supports regex filter, detail-level filter, wrapping
  (one button: no wrap / word wrap / hard wrap at the right edge),
  and clear (truncate file).
- debug(level, msg): writes one line into the app debug log file (filesystem).
- Plugin API (handles / onload / create_tab): open *.log in LogViewerTab.
- viewer polls that file like any other .log.
- main opens the debug log path automatically when -debug is on the CLI.
"""

from __future__ import annotations

import datetime
import inspect
import re
import tkinter as tk
from pathlib import Path
from tkinter import ttk, messagebox
from typing import List, Optional, Tuple  #Callable, 

# ---------------------------------------------------------------------------
# Paths / prefs (lazy utils import to limit cycles)
# ---------------------------------------------------------------------------

def _config_dir() -> Path:
    from utils import CONFIG_DIR, ensure_config_dir
    ensure_config_dir()
    return CONFIG_DIR


def debug_log_path() -> Path:
    return _config_dir() / "debug.log"


PREF_WRAP = "debug_wrap"
# Wrap modes: Tk's text wrap values, with their menu labels.
WRAP_MODES = (("none", "No wrap"), ("word", "Word wrap"), ("char", "Hard wrap (at the right edge)"))


def wrap_mode_from_pref(value) -> str:
    """The saved wrap preference ("none"/"word"/"char"; older versions
    saved True/False for word wrap on/off)."""
    if value is True:
        return "word"
    if value in ("word", "char"):
        return value
    return "none"


def wrap_button_text(mode: str) -> str:
    short = {"none": "No wrap", "word": "Word wrap", "char": "Hard wrap"}
    return f"{short.get(mode, 'No wrap')} \u25be"
PREF_FILTER = "debug_filter"
PREF_DETAIL = "debug_detail_filter"  # max Lnn to show; 0 = all

_LEVEL_RE = re.compile(r"\bL(\d{2})\b")
POLL_MS = 400


def _get_pref(key: str, default):
    try:
        from utils import get_preference
        return get_preference(key, default)
    except Exception:
        return default


def _set_pref(key: str, value) -> None:
    try:
        from utils import set_preference
        set_preference(key, value)
    except Exception:
        pass


# ---------------------------------------------------------------------------
# debug() – filesystem only
# ---------------------------------------------------------------------------

_debug_level: int = 99  #capture everything until told otherwise


def set_debug_level(level: int) -> None:
    """Set max detail written by debug(). 0 = off. Non-zero truncates/creates debug.log and stores the level."""
    global _debug_level
    _debug_level = max(0, min(99, int(level)))
    if _debug_level > 0:
        path = debug_log_path()
        path.parent.mkdir(parents=True, exist_ok=True)
#        from zoneinfo import ZoneInfo
#        local_tz = ZoneInfo("America/Los_Angeles") 
        # Truncate at start of a debug session
        header = (
            f"# debug log started "
#            f"{datetime.datetime.now().astimezone().isoformat(timespec='seconds')} "
            f"{datetime.datetime.now().astimezone().strftime('%Y-%m-%dT%H:%M:%S %z %Z')} "
            f"detail_level={_debug_level}\n\n"
        )
        path.write_text(header, encoding="utf-8")


def get_debug_level() -> int:
    return _debug_level


#def debug(level: int, msg: str) -> None:
def debug(level: int, *args, **kwargs):
    """
    Append one line to the debug log file if level <= current debug level.
    Log if level <= current debug level. Includes caller file:line.
    Add a timestamped entry to the debug log if level <= current debug level.
    level 1 = high-level, 99 = very low-level detail.
    Always buffers; flushes into the Debug tab when it is available.
    Format: [HH:MM:SS.mmm] Lnn  file:line  message
    TODO: add buffering/flush option
    """
    #print(f"debug level {level} vs {_debug_level} wanted: {args[0]}")
    if _debug_level <= 0 or level > _debug_level:
        return args[-1]  #for inlining last arg

    # Caller: skip this frame (debug itself)
    depth = kwargs.pop('depth', 0) + 1
    try:
        frame = inspect.currentframe()
        outer = frame.f_back if frame else None
        # Skip the utils.debug wrapper frame if present
        if outer and Path(outer.f_code.co_filename).name == "utils.py":
            outer = outer.f_back

        #allow nested calls:
        from types import SimpleNamespace as Obj
        #class ObjectLiteral: pass
        frame = inspect.stack()[depth]
        caller_frame_record = inspect.getframeinfo(frame[0])
        #outer = ObjectLiteral()
        #outer.f_lineno = caller_frame_record.lineno
        #outer.f_code =: {co_filename: caller_frame_record.filename}}
        outer = Obj(f_lineno = caller_frame_record.lineno, f_code = Obj(co_filename = caller_frame_record.filename))

        if outer:
            fname = Path(outer.f_code.co_filename).name.replace(".py", "")
            lineno = outer.f_lineno
            caller = f"{fname}:{lineno}"
        else:
            caller = "?:?"
    except Exception as exc:
        caller = f"?:? {exc}"
    finally:
        try:
            del frame  # avoid reference cycles
        except Exception:
            pass

    msg = ""
    for i, arg in enumerate(args):
        msg += str(arg) + " "

    ts = datetime.datetime.now().strftime("%H:%M:%S.%f")[:-3]
#    line = f"[{ts}] L{level:02d}  {caller}  {msg}\n"
    line = f"[{ts}] {msg} @{caller}/L{level:02d}\n" if msg else ""

    import sys
    try:
        path = debug_log_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as f:
            f.write(line)
    except Exception as exc:
        print(f"write {line}: {exc}", file=sys.stderr)
        pass

    return args[-1]  #for inlining last arg


# ---------------------------------------------------------------------------
# Per-tab log-viewer state (stored on the EditorTab instance)
# ---------------------------------------------------------------------------

class _LogViewState:
    def __init__(self, tab, filepath: str):
        self.tab = tab
        self.filepath = str(Path(filepath).resolve())
        self.file_lines: List[str] = []
        self.mtime: float = 0.0
        self.size: int = 0
        self.filter_var: Optional[tk.StringVar] = None
        self.detail_var: Optional[tk.StringVar] = None
        self.wrap_var: Optional[tk.StringVar] = None     # "none" | "word" | "char"
        self.wrap_button = None
        self.status_label: Optional[ttk.Label] = None
        self.controls_window = None  # canvas window id


FILE_TYPES = [("Log files", "*.log")]   # File > Open (tracked.py)


def handles(filepath: str) -> bool:
    if not filepath:
        return False
    return Path(filepath).suffix.lower() == ".log"


def onload(filepath: str, canvas=None, text=None, tab=None) -> bool:
    """
    Claim *.log files. Build controls in canvas; put polled log text in text.
    """
    if not handles(filepath):
        debug(1, f"{{red}}'{filepath}' not log")
        return False   # not handled
    if canvas is None or text is None or tab is None:
        # Claim-only probe (no widgets) – still claim so create_tab paths can use us
        debug(1, f"{{green}}{filepath} is log")
        return True

    state = _LogViewState(tab, filepath)
    tab._log_view_state = state
    tab._plugin_after_id = None

    _build_controls(canvas, text, tab, state)
    _full_reload(text, tab, state)
    _schedule_poll(text, tab, state)

    try:
        from utils import debug as _d
        _d(1, f"{{blue}}log viewer attached to {state.filepath}")
    except Exception:
        pass

    return True


def _build_controls(canvas, text, tab, state: _LogViewState) -> None:
    """Place filter / detail / wrap / clear / reload on the graphical panel."""
    # Host frame inside the canvas so it lays out with the panel
    host = ttk.Frame(canvas)
    state.controls_window = canvas.create_window(0, 0, anchor="nw", window=host)

    def _on_canvas_configure(event, c=canvas, h=host):
        c.itemconfigure(state.controls_window, width=event.width)

    canvas.bind("<Configure>", _on_canvas_configure, add="+")

    row = ttk.Frame(host)
    row.pack(fill="x", padx=4, pady=4)

    ttk.Label(row, text="Filter (regex):").pack(side="left")
    state.filter_var = tk.StringVar(value=str(_get_pref(PREF_FILTER, "") or ""))
    ent = ttk.Entry(row, textvariable=state.filter_var, width=28)
    ent.pack(side="left", padx=(4, 4))
    ent.bind("<KeyRelease>", lambda e: _on_filter_changed(text, state))
    ent.bind("<Return>", lambda e: _on_filter_changed(text, state))

    ttk.Label(row, text="Detail ≤").pack(side="left", padx=(8, 0))
    detail_default = int(_get_pref(PREF_DETAIL, 0) or 0)
    state.detail_var = tk.StringVar(value=str(detail_default))
    spin = ttk.Spinbox(
        row,
        from_=0,
        to=99,
        width=4,
        textvariable=state.detail_var,
        command=lambda: _on_detail_changed(text, state),
    )
    spin.pack(side="left", padx=(4, 0))
    spin.bind("<KeyRelease>", lambda e: _on_detail_changed(text, state))
    spin.bind("<Return>", lambda e: _on_detail_changed(text, state))
    ttk.Label(row, text="(0=all)").pack(side="left", padx=(2, 6))

    state.status_label = ttk.Label(row, text="", foreground="#888888")
    state.status_label.pack(side="left", padx=(4, 8))

    # One button for the wrap choice, with the modes in its menu.
    state.wrap_var = tk.StringVar(value=wrap_mode_from_pref(_get_pref(PREF_WRAP, False)))
    wrap_btn = ttk.Menubutton(row, text=wrap_button_text(state.wrap_var.get()))
    wrap_menu = tk.Menu(wrap_btn, tearoff=False, bg="#ffffff", fg="#1e1e1e", activebackground="#cfe0ff",
                        activeforeground="#1e1e1e", selectcolor="#1e1e1e")
    for mode, label in WRAP_MODES:
        wrap_menu.add_radiobutton(label=label, value=mode, variable=state.wrap_var,
                                  command=lambda: _toggle_wrap(text, state))
    wrap_btn.configure(menu=wrap_menu)
    wrap_btn.pack(side="left", padx=(8, 4))
    state.wrap_button, state.wrap_menu = wrap_btn, wrap_menu

    ttk.Button(
        row, text="Clear", command=lambda: _clear_log(text, tab, state)
    ).pack(side="right", padx=2)
    ttk.Button(
        row, text="Reload", command=lambda: _full_reload(text, tab, state)
    ).pack(side="right", padx=2)

    # Apply the saved wrap mode immediately
    text.configure(wrap=state.wrap_var.get())


def _read_stat(path: str) -> Tuple[float, int]:
    try:
        st = Path(path).stat()
        return st.st_mtime, st.st_size
    except OSError:
        return 0.0, 0


def _full_reload(text, tab, state: _LogViewState) -> None:
    path = Path(state.filepath)
    try:
        if path.is_file():
            data = path.read_text(encoding="utf-8", errors="replace")
            state.file_lines = data.splitlines()
            state.partial_last = bool(data) and not data.endswith(("\n", "\r"))
            state.mtime, state.size = _read_stat(state.filepath)
        else:
            state.file_lines = []
            state.mtime, state.size = 0.0, 0
    except Exception as e:
        state.file_lines = [f"(error reading {state.filepath}: {e})"]
        state.mtime, state.size = 0.0, 0
    _rebuild_view(text, tab, state)


def _schedule_poll(text, tab, state: _LogViewState) -> None:
    if getattr(tab, "_plugin_after_id", None) is not None:
        try:
            tab.frame.after_cancel(tab._plugin_after_id)
        except Exception:
            pass

    def _tick():
        tab._plugin_after_id = None
        try:
            mtime, size = _read_stat(state.filepath)
            if mtime != state.mtime or size != state.size:
                if size < state.size:
                    _full_reload(text, tab, state)
                else:
                    _tail(text, tab, state, size)
                state.mtime, state.size = mtime, size
        except Exception:
            pass
        try:
            tab._plugin_after_id = tab.frame.after(
                POLL_MS, _tick
            )
        except tk.TclError:
            pass

    try:
        tab._plugin_after_id = tab.frame.after(POLL_MS, _tick)
    except tk.TclError:
        tab._plugin_after_id = None


def _tail(text, tab, state: _LogViewState, new_size: int) -> None:
    try:
        with open(state.filepath, "rb") as f:
            f.seek(state.size)
            chunk = f.read().decode("utf-8", errors="replace")
        if not chunk:
            return
        parts = chunk.splitlines()
        # Continue the last line only if it was cut off mid-write (the file
        # didn't end with a newline then); otherwise the new text starts a
        # line of its own -- before, a message that arrived on its own (e.g.
        # "Auto-saved ...") was glued onto the end of the line before it.
        if state.file_lines and getattr(state, "partial_last", False):
            first, *rest = parts if parts else [""]
            state.file_lines[-1] = state.file_lines[-1] + first
            state.file_lines.extend(rest)
        else:
            state.file_lines.extend(parts)
        state.partial_last = not chunk.endswith(("\n", "\r"))
        _rebuild_view(text, tab, state)
    except Exception:
        _full_reload(text, tab, state)


def _line_level(line: str) -> Optional[int]:
    m = _LEVEL_RE.search(line)
    return int(m.group(1)) if m else None


def _filtered_rows(state: _LogViewState) -> List[Tuple[int, str]]:
    pattern = (state.filter_var.get() if state.filter_var else "").strip()
    try:
        max_detail = int(state.detail_var.get() or 0) if state.detail_var else 0
    except ValueError:
        max_detail = 0

    rx = None
    if pattern:
        try:
            rx = re.compile(pattern, re.IGNORECASE)
        except re.error:
            rx = None

    rows = []
    for i, ln in enumerate(state.file_lines, start=1):
        if max_detail > 0:
            lev = _line_level(ln)
            if lev is not None and lev > max_detail:
                continue
        if rx is not None and not rx.search(ln):
            continue
        rows.append((i, ln))
    return rows


def _rebuild_view(text, tab, state: _LogViewState) -> None:
    pattern = (state.filter_var.get() if state.filter_var else "").strip()
    rx_error = None
    if pattern:
        try:
            re.compile(pattern, re.IGNORECASE)
        except re.error as e:
            rx_error = str(e)

    was_at_end = True
    try:
        was_at_end = float(text.yview()[1]) >= 0.99
    except Exception:
        pass

    rows = _filtered_rows(state)

    new_body = "\n".join(ln for _, ln in rows) + ("\n" if rows else "")
    old_body = text.get("1.0", "end-1c")
    if new_body == old_body:
        # Still refresh status / gutter, but do not touch text (keeps selection)
        if state.status_label is not None:
            total = len(state.file_lines)
            if rx_error:
                state.status_label.configure(text=f"Invalid regex: {rx_error}")
            else:
                state.status_label.configure(text=f"{len(rows)} / {total} lines")
        if hasattr(tab, "_update_line_numbers"):
            tab.frame.after_idle(tab._update_line_numbers)
        return

   # save selection if any
    sel = None
    try:
        sel = (text.index("sel.first"), text.index("sel.last"))
    except tk.TclError:
        pass

    # Avoid marking the EditorTab dirty while we refresh
    prev_loading = getattr(tab, "_loading", False)
    tab._loading = True
    text.delete("1.0", "end")
    if rows:
#        text.insert("1.0", "\n".join(ln for _, ln in rows) + "\n")
#        _insert_colored_lines(text, rows)  # see §2
        from utils import insert_styled_text
        body = "\n".join(ln for _, ln in rows) + "\n"
        insert_styled_text(text, body, "end")  #use styled text as-is from file
    else:
        pass
    text.edit_modified(False)
    tab._loading = prev_loading

    if sel is not None:
        try:
            text.tag_add("sel", sel[0], sel[1])
        except tk.TclError:
            pass

    # Original file line numbers for the gutter (non-sequential when filtered)
    tab._gutter_orig_nums = [n for n, _ in rows] if rows else []

    total = len(state.file_lines)
    if state.status_label is not None:
        if rx_error:
            state.status_label.configure(text=f"Invalid regex: {rx_error}")
        else:
            state.status_label.configure(text=f"{len(rows)} / {total} lines")

    # Always refresh line numbers (including lines added since startup via poll)
    if hasattr(tab, "_update_line_numbers"):
        # Prefer original file line numbers when filtered
#        if hasattr(tab, "linenumbers") and rows:
#            tab.linenumbers.configure(state="normal")
#            tab.linenumbers.delete("1.0", "end")
#            nums = [str(n) for n, _ in rows]
#            width = max(4, max((len(x) for x in nums), default=4))
#            tab.linenumbers.configure(width=width)
#            tab.linenumbers.insert("1.0", "\n".join(nums))
#            tab.linenumbers.configure(state="disabled")
#        else:
#            tab._update_line_numbers()
            tab.frame.after_idle(tab._update_line_numbers)

    if was_at_end:
        text.see("end")


def _on_filter_changed(text, state: _LogViewState) -> None:
    if state.filter_var is not None:
        _set_pref(PREF_FILTER, state.filter_var.get())
    _rebuild_view(text, state.tab, state)


def _on_detail_changed(text, state: _LogViewState) -> None:
    try:
        val = int(state.detail_var.get() or 0) if state.detail_var else 0
        val = max(0, min(99, val))
    except ValueError:
        val = 0
    _set_pref(PREF_DETAIL, val)
    _rebuild_view(text, state.tab, state)


def _toggle_wrap(text, state: _LogViewState) -> None:
    mode = wrap_mode_from_pref(state.wrap_var.get()) if state.wrap_var else "none"
    _set_pref(PREF_WRAP, mode)
    text.configure(wrap=mode)
    if state.wrap_button is not None:
        try:
            state.wrap_button.configure(text=wrap_button_text(mode))
        except tk.TclError:
            pass
    tab = state.tab
    if hasattr(tab, "_update_line_numbers"):
        tab.frame.after_idle(tab._update_line_numbers)

def _clear_log(text, tab, state: _LogViewState) -> None:
    if not messagebox.askyesno(
        "Clear log",
        f"Truncate this log file on disk?\n\n{state.filepath}",
        parent=tab.frame.winfo_toplevel(),
    ):
        return
    try:
        Path(state.filepath).write_text("", encoding="utf-8")
    except Exception as e:
        messagebox.showerror("Clear log", str(e))
        return
    _full_reload(text, tab, state)

#eof