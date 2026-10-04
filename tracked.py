#!/usr/bin/env python3
"""
Simple Multi-Tab Editor – main application
Handles menus, keyboard shortcuts, notebook, session restore, drag-and-drop, and lifecycle.
drag-and-drop, tab reordering, and lifecycle.

installation:
pip install tkinterdnd2

structure:
editor/
├── main.py          # Menus, window, notebook, event handling
├── editor_tab.py    # Tab content (Text widget + dirty tracking + close button)
├── logview_tab.py   # Generic log + debug log content
├── image_tab.py     # image viewer/editor
├── audio_tab.py     # audio viewer/editor
└── utils.py         # Helpers (recent files, dialogs, path utilities, etc.)

usage:
# Linux / Windows (any Python 3.8+)
python main.py
# Normal start – restores everything from the single session.json
python main.py

# Start completely clean (ignore previous session)
python main.py -fresh

# Debug log: by default uses the "debug_level" preference (factory
# default 10; also settable in Edit > Preferences). For this run only:
python main.py -debug          # level 1
python main.py -debug 5
python main.py -debug=20
python main.py -nodebug        # off (same as -debug 0)
python main.py -actions        # log every key press / click / menu pick ("ACTION", see UserActionLog)
python main.py -busy           # print "trackED: busy" diagnostics (Preferences has a setting too)
# Change the stored default (and use it now):
python main.py -debug-default 3
python main.py -debug-default=0
python main.py -debug-default  # reset to the factory default (10)

# Open specific files (and still restore session unless -fresh is also given)
python main.py notes.txt todo.md

# Clean start + open files
python main.py -fresh report.txt

# Combine
python main.py -fresh -debug 3 notes.txt

# force recompile:
rm -r __pycache__
"""

from __future__ import annotations

import os
import re
import sys
import datetime
import threading
import time
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import webbrowser
from pathlib import Path
from typing import List, Optional, Union

# ---------------------------------------------------------------------------
# Application constants
# ---------------------------------------------------------------------------
APP_NAME = "trackED"
VERSION = "1.2.0"

# Make the constants available to utils
import utils
utils.APP_NAME = APP_NAME
utils.VERSION = VERSION

from editor_tab import EditorTab
from logview_tab import (
    debug, set_debug_level, get_debug_level, debug_log_path,
#    create_tab as create_debug_tab,
#    LogViewerTab, 
)
from utils import (
    load_recent, add_recent, load_session_data, save_session_data,
    about_text, documentation_url, abbreviated_name,
    get_max_recent, set_preference, get_preference,
    get_default_debug_level, set_default_debug_level, get_autosave_seconds, get_stem_min_seconds,
#    find_create_tab_plugin,
)
#TODO: remove find_create_tab_plugin if main no longer uses create_tab for logs.


# Optional drag-and-drop support (MIT license)
try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    HAS_DND = True
except ImportError:
    HAS_DND = False
    TkinterDnD = None  # type: ignore


# ---------------------------------------------------------------------------
# Custom notebook with a red close (✕) element on every tab
# ---------------------------------------------------------------------------

TAB_ROW_BG = "#b4b4b4"       # empty area of the tab row
TAB_BG = "#d6d6d6"
TAB_ACTIVE_BG = "#e2e2e2"
TAB_SELECTED_BG = "#f2f2f2"


class CustomNotebook(ttk.Notebook):
    """ttk.Notebook with a red close element on every tab."""

    _style_initialized = False

    def __init__(self, *args, **kwargs):
        if not CustomNotebook._style_initialized:
            self._init_style()
            CustomNotebook._style_initialized = True
        kwargs["style"] = "CustomNotebook"
        super().__init__(*args, **kwargs)
        self._active_close = None
        self._close_callback = None          # set by EditorApp after construction
        self.bind("<ButtonPress-1>", self._on_close_press, True)
        self.bind("<ButtonRelease-1>", self._on_close_release)

    def _init_style(self) -> None:
        style = ttk.Style()
        # Build a simple red "X" image via PhotoImage
        # 10x10 pixels, transparent background, red X
        #data = """
        #    R0lGODlhDAAMAIABAMISEv///yH5BAEAAAEALAAAAAAMAAwAAAIdjI+py+0Po5y02ospcFtr
        #    3X1hNJbmKW7pirm2lZ5OASQFADs=
        #"""
        # Fallback: use text-based element if GIF fails; create via tk
        #try:
        #    self._img_close = tk.PhotoImage(data=data)
        #except Exception:
            # Programmatic 10x10 red X
        #    self._img_close = tk.PhotoImage(width=12, height=12)
        #    for x, y in (
        #        (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8),
        #        (8, 2), (7, 3), (6, 4), (5, 5), (4, 6), (3, 7), (2, 8),
        #    ):
        #        self._img_close.put("#c0392b", (x, y))

        # Programmatic 12×12 red X, 2-3 px thick (no external image file needed)
        self._img_close = tk.PhotoImage(width=12, height=12)
        red = "#d0021b"
        for i in range(2, 10):
            for x, y in ((i, i), (i + 1, i), (i, i + 1),                    # "\\" stroke
                         (11 - i, i), (10 - i, i), (11 - i, i + 1)):       # "/" stroke
                if 0 <= x < 12 and 0 <= y < 12:
                    self._img_close.put(red, (x, y))
        self._img_closepressed = self._img_close
        self._img_closeactive = self._img_close

        try:
            style.element_create(
                "close", "image", self._img_close,
                ("active", "pressed", "!disabled", self._img_closepressed),
                ("active", "!disabled", self._img_closeactive),
                border=6, sticky="",
            )
        except tk.TclError:
            pass  # element already exists from a previous instance

        style.layout("CustomNotebook", [("CustomNotebook.client", {"sticky": "nswe"})])
        # A slightly darker strip behind the tabs, so the empty part of the
        # tab row recedes; tabs stay light, the selected one lightest.
        # (Some native themes, e.g. Windows "vista", ignore these colors.)
        style.configure("CustomNotebook", background=TAB_ROW_BG)
        style.configure("CustomNotebook.Tab", background=TAB_BG)
        style.map("CustomNotebook.Tab", background=[("selected", TAB_SELECTED_BG), ("active", TAB_ACTIVE_BG)])
        style.layout("CustomNotebook.Tab", [
            ("CustomNotebook.tab", {
                "sticky": "nswe",
                "children": [
                    ("CustomNotebook.padding", {
                        "side": "top",
                        "sticky": "nswe",
                        "children": [
                            ("CustomNotebook.focus", {
                                "side": "top",
                                "sticky": "nswe",
                                "children": [
                                    ("CustomNotebook.label", {"side": "left", "sticky": ""}),
                                    ("CustomNotebook.close", {"side": "left", "sticky": ""}),
                                ],
                            }),
                        ],
                    }),
                ],
            }),
        ])

    def _on_close_press(self, event):
        element = self.identify(event.x, event.y)
        if "close" in element:
            index = self.index(f"@{event.x},{event.y}")
            self.state(["pressed"])
            self._active_close = index
            return "break"

    def _on_close_release(self, event):
        if not self.instate(["pressed"]):
            return
        element = self.identify(event.x, event.y)
        try:
            index = self.index(f"@{event.x},{event.y}")
        except tk.TclError:
            index = None
        if (
            "close" in element
            and self._active_close is not None
            and self._active_close == index
        ):
            if self._close_callback is not None:
                self._close_callback(index)
        self.state(["!pressed"])
        self._active_close = None

    def DROP_close_tab_by_index(self, index: int) -> None:
        try:
            frames = self.notebook.tabs()
            frame_id = frames[index]
            for tab in list(self.tabs):
                if str(tab.frame) == frame_id:
                    self.close_tab(tab)
                    return
        except Exception as e:
            debug(1, f"Close by index failed: {e}")

    def DROP_open_debug_tab(self) -> None:
        if self._debug_tab is not None:
            return
        tab = DebugTab(self.notebook, on_close_request=self.close_tab)
        self.tabs.append(tab)          # last in our list
        self._debug_tab = tab
        # Ensure it is the last notebook tab
        try:
            self.notebook.insert("end", tab.frame)
        except tk.TclError:
            pass
        # Do NOT select it by default – keep focus on content tabs


# ---------------------------------------------------------------------------
# Main application
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Readable colors for Tk's built-in dialogs
# ---------------------------------------------------------------------------
# The desktop theme hands Tk a light default text color (via X resources,
# read into the option database at "userDefault" priority). Our own
# widgets all set explicit colors, but Tk's built-in dialogs don't: the
# Open/Save file dialog draws its file names in that light color on a
# white list, so they were invisible until selected (the same problem the
# tooltips had). Entries added here at "interactive" priority outrank the
# desktop's, and are scoped by the dialogs' window classes, so the main
# window keeps its current look.
#   TkFDialog     tk_getOpenFile / tk_getSaveFile (filedialog.askopenfilename...)
#   TkChooseDir   tk_chooseDirectory (filedialog.askdirectory)
#   TkColorDialog tk_chooseColor (colorchooser.askcolor)
#   Dialog        tk_messageBox / tk_dialog (messagebox.*)
#   Toplevel      tkinter.simpledialog (askstring/askfloat...) and our own
#                 pop-ups -- ours set explicit colors, which always win.
# File > Open choices: built from what each *_tab.py plugin declares
# (its FILE_TYPES), plus the editor's own text types. Tk's file dialog
# matches case-sensitively on Linux, so upper-case variants are added.
PREF_LAYOUT_SORT_CASE = "xlayout_sort_case"   # read by xlayout_tab.py (PREF_SORT_CASE)
TEXT_FILE_TYPES = [("Text / lyrics", "*.txt *.lrc *.srt")]


def _with_upper(patterns: str) -> str:
    out = []
    for pat in patterns.split():
        for variant in (pat, pat.upper()):
            if variant not in out:
                out.append(variant)
    return " ".join(out)


def open_filetypes() -> list:
    """[("Supported files", all patterns), plugin entries..., text,
    ("All files", "*")] for filedialog.askopenfilename. The plugin part is
    collected once per session (utils.plugin_file_types caches it)."""
    from utils import plugin_file_types
    entries = plugin_file_types() + TEXT_FILE_TYPES
    entries = [(label, _with_upper(pats)) for label, pats in entries]
    every = []
    for _label, pats in entries:
        every += [p for p in pats.split() if p not in every]
    return [("Supported files", " ".join(every))] + entries + [("All files", "*")]


DIALOG_WINDOW_CLASSES = ("TkFDialog", "TkChooseDir", "TkColorDialog", "Dialog", "Toplevel")
DIALOG_FG = "#1e1e1e"
DIALOG_BG = "#f2f2f2"
DIALOG_FIELD_BG = "#ffffff"
# (option, value) pairs; generic ones first, then the per-widget-class
# field backgrounds, so the more specific entries also come last.
DIALOG_OPTIONS = (
    ("background", DIALOG_BG),
    ("foreground", DIALOG_FG),
    ("highlightBackground", DIALOG_BG),
    ("highlightColor", DIALOG_FG),
    ("activeBackground", "#cfe0ff"),
    ("activeForeground", DIALOG_FG),
    ("disabledForeground", "#8a8a8a"),
    ("selectBackground", "#264f78"),
    ("selectForeground", "#ffffff"),
    ("insertBackground", DIALOG_FG),
    ("troughColor", "#d0d0d0"),
    ("selectColor", DIALOG_FIELD_BG),          # check/radio indicator
    ("Entry.background", DIALOG_FIELD_BG),
    ("Spinbox.background", DIALOG_FIELD_BG),
    ("Listbox.background", DIALOG_FIELD_BG),
    ("Text.background", DIALOG_FIELD_BG),
    ("Canvas.background", DIALOG_FIELD_BG),    # the file dialog's file list
)


PREF_INPUT_METHODS = "use_input_methods"
PREF_BUSY_REPORTS = "busy_reports"     # "trackED: busy -- ..." lines on the terminal (off by default)
BUSY_REPORTS_CLI = {"on": None}        # -busy on the command line turns them on for that run


PREF_LOG_ACTIONS = "log_user_actions"
USER_ACTION_LEVEL = 3          # debug level for "ACTION ..." lines (keys, clicks, menu picks)
LOG_ACTIONS_CLI = {"on": None}  # -actions on the command line


def log_actions_on() -> bool:
    if LOG_ACTIONS_CLI["on"] is not None:
        return LOG_ACTIONS_CLI["on"]
    return bool(get_preference(PREF_LOG_ACTIONS, False))


def busy_reports_on() -> bool:
    if BUSY_REPORTS_CLI["on"] is not None:
        return BUSY_REPORTS_CLI["on"]
    return bool(get_preference(PREF_BUSY_REPORTS, False))


def apply_input_methods(root) -> bool:
    """Whether Tk talks to the desktop's X input method (XIM) for typing.

    With ibus (and other XIM servers), Tk sets up an input context for each
    text/entry widget and talks to the input method server synchronously.
    A timing track has several such fields per card, so building or
    switching a track with ~70 cards kept this app waiting on ibus-daemon
    for seconds (busy reports: main loop busy, almost no CPU of our own;
    htop: ibus-daemon). Off by default (Preferences); then Tk reads the
    keyboard directly: plain typing works, but anything the input method
    composes (IME input, and possibly dead-key / Compose-key accents,
    depending on the desktop setup) needs it on."""
    use = bool(get_preference(PREF_INPUT_METHODS, False))
    try:
        root.tk.call("tk", "useinputmethods", "-displayof", root, 1 if use else 0)
    except (tk.TclError, AttributeError):
        pass
    return use


def apply_dialog_colors(root) -> None:
    """Give Tk's built-in dialogs explicit, readable colors (see above).
    Call once, right after the root window is created."""
    for cls in DIALOG_WINDOW_CLASSES:
        for option, value in DIALOG_OPTIONS:
            try:
                root.option_add(f"*{cls}*{option}", value, "interactive")
            except Exception:
                pass


class EditorApp(TkinterDnD.Tk if HAS_DND else tk.Tk):  # type: ignore
    def __init__(
        self,
        files_to_open: Optional[List[str]] = None,
        fresh: bool = False,
        debug_level: Optional[int] = None,
    ):
        super().__init__()
        apply_dialog_colors(self)      # before any dialog can open
        apply_input_methods(self)      # before any text widget is made
        self.title(APP_NAME)
        self.minsize(400, 300)
        self._restore_window_geometry()

#        self.tabs: List[Union[EditorTab, DebugTab]] = []
        self.tabs: List[EditorTab] = []
        self.recent_menu: Optional[tk.Menu] = None
        self._files_to_open = files_to_open or []
        self._fresh = fresh
        self._debug_tab: Optional[EditorTab] = None
        self._last_tab = None

        if debug_level is None:
            debug_level = get_default_debug_level()   # persistent preference
        set_debug_level(debug_level)   # truncates/creates debug.log, stores level
        if debug_level > 0:
            debug(1, f"{{pink}}Starting {APP_NAME} v{VERSION}  debug_level={debug_level}")

        self._build_ui()
#        self._set_window_icon()
#        self.after(100, self._set_window_icon)   # after first map
        self.after(500, self._set_window_icon)   # again once WM is ready
        self._build_menus()
        self._bind_shortcuts()
        self._setup_drag_drop()
        self._setup_tab_reordering()

        # Wire the close-button callback now that the notebook exists
        self.notebook._close_callback = self._close_tab_by_index

        # Restore previous session (unless -fresh) then open any CLI files
        self.after(50, self._startup_open)
        self.protocol("WM_DELETE_WINDOW", self.on_quit)
        # Auto-save: checked every second so a changed interval in
        # Preferences takes effect right away.
        self._last_autosave = time.monotonic()
        self.after(1000, self._autosave_tick)

    # ------------------------------------------------------------------ UI
    def _build_ui(self) -> None:
        self.notebook = CustomNotebook(self)
        self.notebook.pack(fill="both", expand=True)
        self.notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)
#        self.notebook.bind("<<NotebookTabClosed>>", self._on_notebook_tab_closed)

        self.status = ttk.Label(self, text="Ready", relief="sunken", anchor="w")
        # Packed before the notebook: when the window shrinks, pack takes
        # space from the widgets packed last, so the notebook gives way and
        # the status bar stays visible.
        self.status.pack(side="bottom", fill="x", before=self.notebook)

    def _set_window_icon(self) -> None:
        """Set the window decoration icon (title bar / taskbar)."""
        import os
        debug(2, f"{{blue}}desktop", os.environ.get('XDG_CURRENT_DESKTOP'))
        debug(2, f"{{blue}}shell", os.environ.get('SHELL', '/bin/bash')) 
#Wayland vs X11
#Some Wayland sessions never take iconphoto from Tk
#Running under python main.py vs .desktop: Desktop entry Icon= is what the taskbar uses
#wmctrl -l / taskbar: Title bar vs dock can use different icons
        path = Path(__file__).resolve().parent / "app_icon.png"
        try:
            if path.is_file():
                self._app_icon = tk.PhotoImage(file=str(path))
                self.iconphoto(True, self._app_icon)
                debug(1, f"{{blue}}icon from file {path}")
                debug(1, f"{{blue}}Tk {tk.TkVersion}  windowing={self.tk.call('tk', 'windowingsystem')}")
                debug(1, f"{{blue}}iconphoto exists={hasattr(self, 'iconphoto')}")
                debug(1, f"{{blue}}_app_icon ref={getattr(self, '_app_icon', None)}")
                return
        except Exception as exc:
            debug(1, f"{{red}}PNG icon failed: {exc!r}")

        try:
            icon = self._make_app_icon()
            # Keep a reference so Tk does not garbage-collect it
            self._app_icon = icon
            self.iconphoto(True, icon)
            debug(1, f"{{green}}iconphoto OK  size={icon.width()}x{icon.height()}")
        except Exception as exc:
            debug(1, f"{{red}}iconphoto FAILED: {exc!r}")

    def _make_app_icon(self) -> tk.PhotoImage:
        """
        Small programmatic icon (no external file).
        32x32 teal page with a fold — distinctive enough for the title bar.
        """
        size = 32
        img = tk.PhotoImage(width=size, height=size)
        # Background
        bg, accent, line = "#2c3e50", "#1abc9c", "#ecf0f1"
        for y in range(size):
            for x in range(size):
                img.put(bg, (x, y))
        # Page rectangle
        for y in range(4, 28):
            for x in range(6, 26):
                img.put(line, (x, y))
        # Fold corner
        for i in range(8):
            for x in range(18 + i, 26):
                img.put(accent, (x, 4 + i))
        # Text lines
        for y in (12, 16, 20, 24):
            for x in range(9, 23):
                img.put(accent if y != 24 else "#3498db", (x, y))
        return img

    def DROP_on_notebook_tab_closed(self, event=None) -> None:
        # event.x / identify already handled; find tab by current close target
        try:
            # After release the selection may still be the closed tab's neighbor;
            # use the index stored during press via a short lookup
            idx = self.notebook._active_close
            if idx is None:
                # fallback: close current
                self.close_current()
                return
            # Map index → our tab object
            frames = list(self.notebook.tabs())
            if 0 <= idx < len(frames):
                frame_id = frames[idx]
                for tab in list(self.tabs):
                    if str(tab.frame) == frame_id:
                        self.close_tab(tab)
                        return
        except Exception:
            self.close_current()

    def _build_menus(self) -> None:
        menubar = tk.Menu(self)

        # ----- File -----
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="New", accelerator="Ctrl+N", command=self.new_file)
        file_menu.add_command(label="Open…", accelerator="Ctrl+O", command=self.open_file)
        self.recent_menu = tk.Menu(file_menu, tearoff=0)
        file_menu.add_cascade(label="Open Recent", menu=self.recent_menu)
        self._rebuild_recent_menu()
        file_menu.add_separator()
        file_menu.add_command(label="Save", accelerator="Ctrl+S", command=self.save_file)
        file_menu.add_command(label="Save As…", accelerator="Ctrl+Shift+S", command=self.save_file_as)
        file_menu.add_separator()
        file_menu.add_command(label="Close", accelerator="Ctrl+W", command=self.close_current)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", accelerator="Alt+F4", command=self.on_quit)
        menubar.add_cascade(label="File", menu=file_menu)

        # ----- Edit -----
        edit_menu = tk.Menu(menubar, tearoff=0)
        edit_menu.add_command(label="Undo", accelerator="Ctrl+Z", command=self.undo)
        edit_menu.add_command(label="Redo", accelerator="Ctrl+Y", command=self.redo)
        edit_menu.add_separator()
        edit_menu.add_command(label="Cut", accelerator="Ctrl+X", command=lambda: self._text_event("<<Cut>>"))
        edit_menu.add_command(label="Copy", accelerator="Ctrl+C", command=lambda: self._text_event("<<Copy>>"))
        edit_menu.add_command(label="Paste", accelerator="Ctrl+V", command=lambda: self._text_event("<<Paste>>"))
        edit_menu.add_separator()
        edit_menu.add_command(label="Find…", accelerator="Ctrl+F", command=self.find)
        edit_menu.add_command(label="Replace…", accelerator="Ctrl+H", command=self.replace)
        edit_menu.add_separator()
        edit_menu.add_command(label="Preferences…", command=self.show_preferences)
        menubar.add_cascade(label="Edit", menu=edit_menu)

        # ----- Help -----
        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="Keyboard Shortcuts", accelerator="F1", command=self.show_shortcuts)
        help_menu.add_command(label="Documentation / Tutorials", command=self.open_docs)
        help_menu.add_command(label="Check for Updates", command=self.check_updates)
        help_menu.add_separator()
        help_menu.add_command(label="About", command=self.show_about)
        menubar.add_cascade(label="Help", menu=help_menu)

        self.config(menu=menubar)

    def _bind_shortcuts(self) -> None:
        self.bind_all("<F1>", lambda e: self.show_shortcuts())
        self.bind_all("<Control-n>", lambda e: self.new_file())
        self.bind_all("<Control-o>", lambda e: self.open_file())
        self.bind_all("<Control-s>", lambda e: self.save_file())
        self.bind_all("<Control-S>", lambda e: self.save_file_as())  # Shift
        self.bind_all("<Control-w>", lambda e: self.close_current())
        # Deliberately NOT bound here: Ctrl-Z/Ctrl-Y. EditorTab's Text
        # widget is created with undo=True, which gives it Tk's own
        # native Ctrl-Z/Ctrl-Y key bindings (built into every Text
        # widget, independent of anything this app binds). Having
        # bind_all ALSO call self.undo()/self.redo() on the very same
        # keypress meant every Ctrl-Z fired twice -- Tk's native binding
        # plus this one -- silently undoing two steps (or erroring past
        # the end of the stack) instead of one. Since a menu click
        # doesn't trigger Tk's native key binding, Edit > Undo/Redo still
        # work correctly via self.undo()/self.redo() with no change; only
        # the keyboard shortcut needed to go, and the Text widget's own
        # binding covers it. (waveform_tab.py's canvas -- a plain Canvas,
        # with no native undo binding of its own -- binds Ctrl-Z/Ctrl-Y
        # directly on itself instead, for its marks/tracks undo; that's
        # the one place this app-wide bind_all approach was never safe.)
#no        self.bind_all("<Control-z>", lambda e: self.undo())
#no        self.bind_all("<Control-y>", lambda e: self.redo())
        self.bind_all("<Control-f>", lambda e: self.find())
        self.bind_all("<Control-h>", lambda e: self.replace())
        # Platform-specific quit
        self.bind_all("<Alt-F4>", lambda e: self.on_quit())

    def _setup_drag_drop(self) -> None:
        if not HAS_DND:
            debug(1, "{yellow}Drag-and-drop is off: tkinterdnd2 is not installed (use the Install button)")
            return
        # Accept file drops on the whole window / notebook (and each tab's
        # own widgets, see _register_drops -- on Windows a drop goes to the
        # widget under the pointer).
        self._register_drops(self)
        self._register_drops(self.notebook)

    def _register_drops(self, widget) -> None:
        """Make widget a file-drop target that opens dropped files, unless
        it already handles drops itself (the waveform canvas sets
        _own_drop) or was registered before. The Enter/Position handlers
        return the action, so the source (Explorer, a file manager) shows a
        copy cursor rather than "not allowed"."""
        if not HAS_DND or widget is None or getattr(widget, "_own_drop", False) \
                or getattr(widget, "_drop_registered", False):
            return
        try:
            widget.drop_target_register(DND_FILES)
            widget.dnd_bind("<<DropEnter>>", lambda e: getattr(e, "action", "copy") or "copy")
            widget.dnd_bind("<<DropPosition>>", lambda e: getattr(e, "action", "copy") or "copy")
            widget.dnd_bind("<<Drop>>", self._on_drop)
            widget._drop_registered = True
        except (tk.TclError, AttributeError) as exc:
            debug(2, f"drop target not registered on {widget}: {exc}")

    def _register_tab_drops(self, tab) -> None:
        for name in ("frame", "text", "canvas", "linenumbers"):
            self._register_drops(getattr(tab, name, None))

    def _on_drop(self, event) -> str:
        """Open every dropped file in its own tab."""
        data = getattr(event, "data", "")
        debug(2, f"Drop: {data!r}")
        try:
            paths = self.tk.splitlist(data)
        except Exception:
            paths = [data]
        for p in paths:
            p = str(p).strip("{}")  # Windows sometimes wraps paths in braces
            if p and Path(p).is_file():
                self.open_file(p)
                debug(2, f"Dropped file {p}")
            elif p:
                debug(1, f"{{yellow}}Dropped item is not a file: {p}")
        return getattr(event, "action", "copy") or "copy"

    # ------------------------------------------------------------------ Tab reordering
    def _setup_tab_reordering(self) -> None:
        """Allow the user to drag tabs left/right to change their order."""
        self.notebook.bind("<B1-Motion>", self._on_tab_drag)

    def _on_tab_drag(self, event) -> None:
        try:
            index = self.notebook.index(f"@{event.x},{event.y}")
            self.notebook.insert(index, child=self.notebook.select())
            self._keep_debug_last()          # nothing goes right of debug.log
        except tk.TclError:
            pass  # mouse is not over a tab

    # ------------------------------------------------------------------ Close button → tab object
    def _close_tab_by_index(self, index: int) -> None:
        """Called by CustomNotebook when the user clicks the red ✕ on a tab."""
        try:
            frames = self.notebook.tabs()
            if not (0 <= index < len(frames)):
                return
            frame_id = frames[index]
            for tab in list(self.tabs):
                if str(tab.frame) == frame_id:
                    self.close_tab(tab)
                    return
        except Exception as e:
            debug(1, f"Close by index failed: {e}")

    # ------------------------------------------------------------------ Startup
    def _startup_open(self) -> None:
        opened_any = False
        session = load_session_data()
        active_index = session.get("active_index", 0)

        # 1. Restore previous session (unless -fresh)
        if not self._fresh:
            paths = session.get("open_files", [])
            for path in paths:
                if Path(path).is_file():
                    self.open_file(path)
                    opened_any = True
            debug(1, f"{{blue}}Restored session with {len(paths)} file(s)")

        # 2. Files named on the command line
        for path in self._files_to_open:
            if Path(path).is_file():
                self.open_file(path)
                opened_any = True
                debug(1, f"CLI open {path}")

        # 3. At least one empty tab if nothing else
        if not opened_any:
            self.new_file()

        # 4. Debug tab is created LAST so it appears as the rightmost tab
        if get_debug_level() > 0:
            self._open_debug_tab()
        self._keep_debug_last()
#            opened_any = True

        # Restore which tab had focus (EditorTabs only)
        try:
            # skip debug tab if it is first
            # the same list _collect_session counted: tabs with a file
            real_tabs = [t for t in self.tabs if isinstance(t, EditorTab) and t.filepath]
            if real_tabs and 0 <= active_index < len(real_tabs):
                self.notebook.select(real_tabs[active_index].frame)
                real_tabs[active_index].focus()
                real_tabs[active_index].restore_cursor_state()
                debug(2, f"{{blue}}Restored focus to tab index {active_index}")
        except Exception as e:
            debug(1, f"Focus restore failed: {e}")

        self._update_title()

    def _open_debug_tab(self) -> None:
        """Open the app debug.log through the normal EditorTab + onload plugin path."""
        if self._debug_tab is not None:
            return
        from logview_tab import debug_log_path
        path = str(debug_log_path())
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        if not Path(path).exists():
            Path(path).write_text("", encoding="utf-8")
        already = self._debug_log_tab()
        if already is not None:              # reopened by the session: adopt it
            self._debug_tab = already
            self._keep_debug_last()
            return
        # Reuse open_file so EditorTab + debug_tab.onload run
        before = list(self.tabs)
        self.open_file(path)
        # Remember the tab that was just opened (for “last tab” / close tracking)
        for t in self.tabs:
            if t not in before and isinstance(t, EditorTab) and t.filepath == path:
                self._debug_tab = t
                try:
                    self.notebook.insert("end", t.frame)
                except tk.TclError:
                    pass
                break

    def OLD_open_debug_tab(self) -> None:
        if self._debug_tab is not None:
            return
        tab = DebugTab(self.notebook, on_close_request=self.close_tab)
        self.tabs.append(tab)               # keep it last in our list
        self._debug_tab = tab
        # Force it to the end of the notebook
        try:
            self.notebook.insert("end", tab.frame)
        except tk.TclError:
            pass
        # Do not auto-select the debug tab

    # ------------------------------------------------------------------ Tab helpers
    def current_tab(self) -> Optional[EditorTab]: #Union[EditorTab, DebugTab]]:
        try:
            current = self.notebook.select()
            for tab in self.tabs:
                if str(tab.frame) == current:
                    return tab
        except tk.TclError:
            pass
        return None

    def new_file(self) -> None:
        self._new_file_impl()
        self._keep_debug_last()

    def _debug_log_tab(self):
        """The tab showing debug.log: the app's own debug tab, or debug.log
        opened as a file (e.g. reopened by the last session)."""
        dbg = getattr(self, "_debug_tab", None)
        if dbg is not None and dbg in self.tabs:
            return dbg
        try:
            target = str(Path(debug_log_path()).resolve())
        except Exception:
            return None
        for t in self.tabs:
            path = getattr(t, "filepath", None)
            if path:
                try:
                    if str(Path(path).resolve()) == target:
                        return t
                except OSError:
                    pass
        return None

    def _keep_debug_last(self) -> None:
        """Whenever debug.log is open, its tab is the right-most."""
        finder = getattr(self, "_debug_log_tab", None)
        dbg = finder() if callable(finder) else getattr(self, "_debug_tab", None)
        if dbg is None:
            return
        try:
            tabs = self.notebook.tabs()
            if tabs and str(tabs[-1]) != str(dbg.frame):
                self.notebook.insert("end", dbg.frame)
            if dbg in self.tabs and self.tabs[-1] is not dbg:
                self.tabs.remove(dbg)
                self.tabs.append(dbg)
        except (tk.TclError, AttributeError):
            pass

    def _new_file_impl(self) -> None:
        tab = EditorTab(
            self.notebook,
            on_modified=self._on_tab_modified,
            on_close_request=self.close_tab,
        )
        # Insert before the debug tab if it exists
        if self._debug_tab is not None:
            try:
                dbg_index = self.notebook.index(self._debug_tab.frame)
                self.notebook.insert(dbg_index, tab.frame)
                # Keep self.tabs order roughly matching notebook order
                if self._debug_tab in self.tabs:
                    pos = self.tabs.index(self._debug_tab)
                    self.tabs.insert(pos, tab)
                else:
                    self.tabs.append(tab)
            except tk.TclError:
                self.tabs.append(tab)
        else:
            self.tabs.append(tab)
        self.notebook.select(tab.frame)
        tab.focus()
        self._update_title()
        debug(2, "New untitled tab")

    def open_file(self, path: Optional[str] = None) -> None:
        try:
            self._open_file_impl(path)
        finally:
            self._keep_debug_last()

    def _open_file_impl(self, path: Optional[str] = None) -> None:
        if path is None:
            path = filedialog.askopenfilename(
                title="Open File",
                filetypes=open_filetypes(),
            )
        if not path:
            return
        path = str(Path(path).resolve())

        # Reuse existing tab if already open
        for tab in self.tabs:
            if isinstance(tab, EditorTab) and tab.filepath and Path(tab.filepath) == Path(path):
                self.notebook.select(tab.frame)
                return

        # Custom tab plugins (e.g. debug_tab for *.log)
#needed?        found = find_create_tab_plugin(path)
        found = None
        if found is not None:
            _mod, create_fn = found
            tab = create_fn(
                self.notebook,
                filepath=path,
                on_close_request=self.close_tab,
                live_debug=False,
            )
            if tab is not None:
                # insert before debug tab if present (same as EditorTab)
                if self._debug_tab is not None:
                    try:
                        dbg_index = self.notebook.index(self._debug_tab.frame)
                        self.notebook.insert(dbg_index, tab.frame)
                        pos = self.tabs.index(self._debug_tab)
                        self.tabs.insert(pos, tab)
                    except (tk.TclError, ValueError):
                        self.tabs.append(tab)
                else:
                    self.tabs.append(tab)
                self.notebook.select(tab.frame)
                add_recent(path)
                self._rebuild_recent_menu()
                if hasattr(tab, "focus"):
                    tab.focus()
                self._update_title()
                debug(1, f"Opened via plugin {getattr(_mod, '__name__', '?')}: {path}")
                return

        tab = EditorTab(
            self.notebook,
            filepath=path,
            on_modified=self._on_tab_modified,
            on_close_request=self.close_tab,
        )
        if tab.filepath:  # successfully loaded
            if self._debug_tab is not None:
                try:
                    dbg_index = self.notebook.index(self._debug_tab.frame)
                    self.notebook.insert(dbg_index, tab.frame)
                    if self._debug_tab in self.tabs:
                        pos = self.tabs.index(self._debug_tab)
                        self.tabs.insert(pos, tab)
                    else:
                        self.tabs.append(tab)
                except tk.TclError:
                    self.tabs.append(tab)
            else:
                self.tabs.append(tab)
            self.notebook.select(tab.frame)
            add_recent(path)
            self._rebuild_recent_menu()
            tab.focus()
            self._update_title()
        else:
            tab.destroy()

    def save_file(self) -> bool:
        """
        Saving:
        For files on disk without visible tag markers left as-is, use get_content() to save
        (tags are only stripped in the display path if strip_style_tags was used on save)
        Tags should normally be left in the file so reload still colors).
        Default:
        save raw buffer text including {red} markers (what the user typed).
        Display applies styles on insert/load.  If the buffer holds already-expanded text without
        markers (because insert stripped them), saving won’t preserve tags. Currently markers are
        stripped on display only while inserting styled runs (so Text widget does not contain {red}).
        For log files that is correct (file on disk still has tags; viewer re-parses each reload).
        For editable tabs, either:
        A. Store tags in the widget as real characters and only apply tags via a highlighter pass, or  
        B. Accept that styled insert is for read-only/plugin/log content.

        For log viewer (file-based) path B is used.
        For editable tab load, path B will strip file’s {red} markers after load.
        To keep them editable, run a highlighter over existing text instead of stripping on insert.
        """
        return self._save_tab(self.current_tab(), interactive=True)

    def _save_tab(self, tab, interactive: bool = True) -> bool:
        """The one save path, used by File > Save, the close/quit prompts
        and auto-save.
          - tab.save_hook (plugin views such as audio): the plugin saves its
            own changes (timing marks -> the sidecar cache); the media file
            itself is never written.
          - tab.protect_file with no hook (e.g. images): the text panel is
            just a description -- nothing to save, never written over the file.
          - otherwise: write the text to the file.
        interactive=False (auto-save) never shows dialogs and skips
        untitled tabs."""
        if not isinstance(tab, EditorTab):
            return False
        hook = getattr(tab, "save_hook", None)
        if hook is not None:
            try:
                ok = bool(hook())
            except Exception as e:
                ok = False
                if interactive:
                    messagebox.showerror("Save Error", str(e))
                debug(1, f"Save failed: {e}")
            if ok:
                tab.mark_clean()
                self.set_status(f"Saved changes for {abbreviated_name(tab.filepath)}")
                self._update_title()
            return ok
        if getattr(tab, "protect_file", False):
            # The text panel is a generated view; writing it to tab.filepath
            # would destroy the file.
            if interactive:
                messagebox.showinfo("Save", "This file is shown through a plugin view and has "
                                            "nothing to save as text.")
            return False
        if not tab.filepath:
            return self.save_file_as() if interactive else False
        try:
            Path(tab.filepath).write_text(tab.get_content(), encoding="utf-8")
            tab.mark_clean()
            add_recent(tab.filepath)
            self._rebuild_recent_menu()
            self.set_status(f"Saved {tab.filepath}")
            self._update_title()
            debug(1, f"Saved {tab.filepath}")
            return True
        except Exception as e:
            if interactive:
                messagebox.showerror("Save Error", str(e))
            debug(1, f"Save failed: {e}")
            return False

    # ------------------------------------------------------------------ window size
    def _restore_window_geometry(self) -> None:
        """Last session's window size/position (kept on screen), and
        maximized state; 1000x700 the first time."""
        geom = get_preference("window_geometry", None)
        m = re.match(r"^(\d+)x(\d+)([+-]-?\d+)([+-]-?\d+)$", geom or "")
        if m:
            w, h = int(m.group(1)), int(m.group(2))
            x, y = int(m.group(3)), int(m.group(4))
            sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
            w, h = max(400, min(w, sw)), max(300, min(h, sh))
            x = max(0, min(x, sw - 100))
            y = max(0, min(y, sh - 100))
            self.geometry(f"{w}x{h}+{x}+{y}")
        else:
            self.geometry("1000x700")
        if get_preference("window_maximized", False):
            try:
                self.state("zoomed")               # Windows / macOS
            except tk.TclError:
                try:
                    self.attributes("-zoomed", True)   # X11
                except tk.TclError:
                    pass

    def _save_window_geometry(self) -> None:
        try:
            maximized = self.state() == "zoomed"
            if not maximized:
                try:
                    maximized = bool(self.attributes("-zoomed"))
                except tk.TclError:
                    pass
            set_preference("window_maximized", maximized)
            if not maximized:   # keep the normal size for when it's un-maximized
                set_preference("window_geometry", self.geometry())
        except tk.TclError:
            pass

    def _autosave_tick(self) -> None:
        """Every second: save each dirty tab whose FIRST unsaved change is
        at least the Preferences interval old (tab.dirty_since) -- so the
        delay always runs from the change, per tab, not from a global
        timer. Same path as File > Save; plugin views like audio save only
        their sidecar data."""
        try:
            interval = get_autosave_seconds()
            now = time.monotonic()
            saved = []
            if interval > 0:
                for tab in list(self.tabs):
                    if not (isinstance(tab, EditorTab) and tab.dirty and tab is not self._debug_tab
                            and (tab.filepath or getattr(tab, "save_hook", None))):
                        continue
                    since = getattr(tab, "dirty_since", None)
                    if since is None:          # dirty without a timestamp: start counting now
                        tab.dirty_since = now
                        continue
                    if now - since >= interval and self._save_tab(tab, interactive=False):
                        saved.append(tab)
                    elif hasattr(tab, "update_tab_label"):
                        tab.update_tab_label((now - since) / interval)   # advance the countdown dial
            if saved:
                names = ", ".join(abbreviated_name(t.filepath) for t in saved)
                self.set_status(f"Auto-saved {names}")
                debug(2, f"Auto-saved {names}")
        finally:
            self.after(1000, self._autosave_tick)

    def save_file_as(self) -> bool:
        tab = self.current_tab()
        if not isinstance(tab, EditorTab):
            return False
        path = filedialog.asksaveasfilename(
            title="Save As",
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
        )
        if not path:
            return False
        if getattr(tab, "protect_file", False):
            # Export the panel text as a copy; the tab stays on its audio file.
            try:
                Path(path).write_text(tab.get_content(), encoding="utf-8")
                self.set_status(f"Saved text copy to {path}")
                return True
            except Exception as e:
                messagebox.showerror("Save Error", str(e))
                return False
        tab.set_filepath(path)
        return self.save_file()

    def close_tab(self, tab: Optional[EditorTab] = None) -> None: #Union[EditorTab, DebugTab]] = None) -> None:
        if tab is None:
            tab = self.current_tab()
        if not tab:
            return

        hook = getattr(tab, "before_close_hook", None)
        if callable(hook):
            if isinstance(tab, EditorTab):
                self.notebook.select(tab.frame)
            if not hook():          # e.g. a question about unassigned timing marks; False = cancel
                return

        if isinstance(tab, EditorTab) and tab.dirty:
            name = abbreviated_name(tab.filepath)
            answer = messagebox.askyesnocancel(
                "Unsaved Changes",
                f'"{name}" has unsaved changes.\nDo you want to save them?',
            )
            if answer is None:  # Cancel
                return
            if answer:  # Yes
                # Temporarily select the tab so save_file works on it
                self.notebook.select(tab.frame)
                if not self.save_file():
                    return

        if tab is self._debug_tab:
            self._debug_tab = None

        tab.destroy()
        if tab in self.tabs:
            self.tabs.remove(tab)

        # Never leave the UI empty
        if not self.tabs:
            self.new_file()
        self._update_title()

    def close_current(self) -> None:
        self.close_tab()

    def set_status(self, message: str) -> None:
        """A message in the status bar, stamped with the date and time it
        appeared (it stays until replaced)."""
        stamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        try:
            self.status.configure(text=f"{message}   ({stamp})" if message else "")
        except tk.TclError:
            pass

    def _on_tab_modified(self, tab: EditorTab) -> None:
        self._update_title()
        # new unsaved changes: an "Auto-saved ..." note no longer applies
        try:
            if getattr(tab, "dirty", False) and "Auto-saved" in str(self.status.cget("text")):
                self.status.configure(text="")
        except (tk.TclError, AttributeError):
            pass

    def _on_tab_changed(self, event=None) -> None:
        # Preserve tab selection when leaving / returning
        prev = self._last_tab  #getattr(self, "_last_tab", None)
        cur = self.current_tab()
        if isinstance(prev, EditorTab):
            prev.save_selection_state()
        if isinstance(cur, EditorTab):
            cur.restore_selection_state()
        self._last_tab = cur
        if isinstance(cur, EditorTab):
            self._register_tab_drops(cur)
        self._update_title()

    def _update_title(self) -> None:
        tab = self.current_tab()
        if isinstance(tab, EditorTab) and tab.filepath:
            name = abbreviated_name(tab.filepath, 40)
            detail = getattr(tab, "title_detail", None)
            if detail:  # e.g. an audio file's total duration
                name = f"{name} ({detail})"
            dirty = " *" if tab.dirty else ""
            self.title(f"{name}{dirty} – {APP_NAME}")
#        elif isinstance(tab, DebugTab):
#            self.title(f"Debug Log – {APP_NAME}")
        else:
            dirty = " *" if (isinstance(tab, EditorTab) and tab.dirty) else ""
            self.title(f"Untitled{dirty} – {APP_NAME}")

    def _rebuild_recent_menu(self) -> None:
        if not self.recent_menu:
            return
        self.recent_menu.delete(0, "end")
        recent = load_recent()
        if not recent:
            self.recent_menu.add_command(label="(empty)", state="disabled")
            return
        for p in recent:
            self.recent_menu.add_command(
                label=p,
                command=lambda path=p: self.open_file(path),
            )
        self.recent_menu.add_separator()
        self.recent_menu.add_command(label="Clear Recent", command=self._clear_recent)

    def _clear_recent(self) -> None:
        from utils import save_recent
        save_recent([])
        self._rebuild_recent_menu()
        debug(2, "Recent list cleared")

    # ------------------------------------------------------------------ Preferences
    def show_preferences(self) -> None:
        win = tk.Toplevel(self)
        win.title("Preferences")
        win.transient(self)
        win.grab_set()
        win.resizable(False, False)

        frm = ttk.Frame(win, padding=12)
        frm.grid(row=0, column=0, sticky="nsew")

        ttk.Label(frm, text="Maximum recent files:").grid(row=0, column=0, sticky="w", pady=4)
        max_var = tk.StringVar(value=str(get_max_recent()))
        spin = ttk.Spinbox(frm, from_=1, to=100, width=6, textvariable=max_var)
        spin.grid(row=0, column=1, sticky="w", padx=(8, 0), pady=4)

        ttk.Label(frm, text="Default debug level:").grid(row=1, column=0, sticky="w", pady=4)
        dbg_var = tk.StringVar(value=str(get_default_debug_level()))
        dbg_spin = ttk.Spinbox(frm, from_=0, to=99, width=6, textvariable=dbg_var)
        dbg_spin.grid(row=1, column=1, sticky="w", padx=(8, 0), pady=4)
        ttk.Label(frm, text="(0 = off; takes effect next start;\n -debug N on the command line overrides)",
                  foreground="#666666").grid(row=2, column=0, columnspan=2, sticky="w")

        ttk.Label(frm, text="Auto-save every (seconds):").grid(row=3, column=0, sticky="w", pady=(10, 4))
        auto_var = tk.StringVar(value=str(get_autosave_seconds()))
        ttk.Spinbox(frm, from_=0, to=3600, width=6, textvariable=auto_var).grid(
            row=3, column=1, sticky="w", padx=(8, 0), pady=(10, 4))
        ttk.Label(frm, text="(0 = off. Text files are written; audio files only save\n"
                            " their marks/tracks sidecar -- the audio is never touched)",
                  foreground="#666666").grid(row=4, column=0, columnspan=2, sticky="w")

        ttk.Label(frm, text="Shortest stem region (seconds):").grid(row=5, column=0, sticky="w", pady=(10, 4))
        stem_var = tk.StringVar(value=f"{get_stem_min_seconds():g}")
        ttk.Spinbox(frm, from_=0, to=30, increment=0.25, width=6, textvariable=stem_var).grid(
            row=5, column=1, sticky="w", padx=(8, 0), pady=(10, 4))
        ttk.Label(frm, text="(shorter vocal / instrumental changes are merged into their\n"
                            " neighbors; applies to audio tabs right away)",
                  foreground="#666666").grid(row=6, column=0, columnspan=2, sticky="w")

        case_var = tk.BooleanVar(value=bool(get_preference(PREF_LAYOUT_SORT_CASE, True)))
        ttk.Checkbutton(frm, text="Case-sensitive sorting in xLights layout lists", variable=case_var).grid(
            row=7, column=0, columnspan=2, sticky="w", pady=(10, 0))
        ttk.Label(frm, text="(on: \"Zebra\" before \"apple\", as in xLights)",
                  foreground="#666666").grid(row=8, column=0, columnspan=2, sticky="w")

        ttk.Label(frm, text="Start before a rising edge (seconds):").grid(row=9, column=0, sticky="w",
                                                                          pady=(10, 4))
        lead_var = tk.StringVar(value=f"{utils.get_edge_lead_in():g}")
        ttk.Spinbox(frm, from_=0, to=2, increment=0.05, width=6, textvariable=lead_var).grid(
            row=9, column=1, sticky="w", padx=(8, 0), pady=(10, 4))
        ttk.Label(frm, text="(cards' \u2196/\u2197 put Start this much before the detected edge --\n"
                            " the sound usually starts a little earlier)",
                  foreground="#666666").grid(row=10, column=0, columnspan=2, sticky="w")

        im_var = tk.BooleanVar(value=bool(get_preference(PREF_INPUT_METHODS, False)))
        ttk.Checkbutton(frm, text="Use the desktop's input method (IME, e.g. ibus) in text fields",
                        variable=im_var).grid(row=11, column=0, columnspan=2, sticky="w", pady=(10, 0))
        ttk.Label(frm, text="(off: much faster with many timing cards; on: needed for IME typing and\n"
                            " possibly dead-key/Compose accents -- fully applies after a restart)",
                  foreground="#666666").grid(row=12, column=0, columnspan=2, sticky="w")

        act_var = tk.BooleanVar(value=bool(get_preference(PREF_LOG_ACTIONS, False)))
        ttk.Checkbutton(frm, text="Log my keys, clicks and menu picks to the debug log (\"ACTION\" lines)",
                        variable=act_var).grid(row=19, column=0, columnspan=2, sticky="w", pady=(10, 0))
        ttk.Label(frm, text=f"(for reproducing a problem: filter the log for ACTION; logged at level "
                            f"{USER_ACTION_LEVEL}, so the debug level must be {USER_ACTION_LEVEL} or more)",
                  foreground="#666666").grid(row=20, column=0, columnspan=2, sticky="w")
        busy_var = tk.BooleanVar(value=bool(get_preference(PREF_BUSY_REPORTS, False)))
        ttk.Checkbutton(frm, text="Print busy reports on the terminal (for diagnosing slowness)",
                        variable=busy_var).grid(row=13, column=0, columnspan=2, sticky="w", pady=(10, 0))
        ttk.Label(frm, text="(\"trackED: busy -- main loop ...\"; also -busy on the command line.\n"
                            " Reports of a frozen window are always printed.)",
                  foreground="#666666").grid(row=14, column=0, columnspan=2, sticky="w")

        bak_var = tk.BooleanVar(value=bool(get_preference("backup_sidecars", False)))
        ttk.Checkbutton(frm, text="Back up each audio file's sidecar (-tracked.json) when it's first opened",
                        variable=bak_var).grid(row=15, column=0, columnspan=2, sticky="w", pady=(10, 0))
        ttk.Label(frm, text="(e.g. song-tracked-20261003-141500.json; only the newest backup is kept)",
                  foreground="#666666").grid(row=16, column=0, columnspan=2, sticky="w")
        repo_var = tk.StringVar(value=str(get_preference("update_repo", "") or ""))
        ttk.Label(frm, text="Updates from GitHub repository (owner/name; empty = default):").grid(
            row=17, column=0, sticky="w", pady=(10, 0))
        ttk.Entry(frm, textvariable=repo_var, width=28).grid(row=17, column=1, sticky="w", padx=(8, 0), pady=(10, 0))

        def on_ok():
            set_preference(PREF_BUSY_REPORTS, bool(busy_var.get()))
            set_preference(PREF_LOG_ACTIONS, bool(act_var.get()))
            set_preference("backup_sidecars", bool(bak_var.get()))
            set_preference("update_repo", repo_var.get().strip())
            try:
                val = int(max_var.get())
                val = max(1, min(val, 100))
            except ValueError:
                val = 10
            set_preference("max_recent", val)
            try:
                set_default_debug_level(int(dbg_var.get()))
            except ValueError:
                pass
            try:
                set_preference("autosave_seconds", max(0, min(3600, int(auto_var.get()))))
            except ValueError:
                pass
            try:
                set_preference("stem_min_seconds", max(0.0, min(30.0, float(stem_var.get()))))
                for t in self.tabs:          # re-smooth open audio tabs' stem regions
                    ctl = getattr(getattr(t, "canvas", None), "_waveform_controller", None)
                    if ctl is not None:
                        ctl.resmooth_regions()
            except ValueError:
                pass
            self.set_layout_sort_case(bool(case_var.get()))
            if bool(im_var.get()) != bool(get_preference(PREF_INPUT_METHODS, False)):
                set_preference(PREF_INPUT_METHODS, bool(im_var.get()))
                apply_input_methods(self)
            try:
                set_preference("edge_lead_in", max(0.0, min(2.0, float(lead_var.get()))))
            except ValueError:
                pass
            from utils import save_recent
            save_recent(load_recent())
            self._rebuild_recent_menu()
            debug(2, f"Preference max_recent set to {val}")
            win.destroy()

        def on_cancel():
            win.destroy()

        btn_frm = ttk.Frame(frm)
        btn_frm.grid(row=21, column=0, columnspan=2, pady=(12, 0), sticky="e")
        ttk.Button(btn_frm, text="OK", command=on_ok).pack(side="right", padx=(4, 0))
        ttk.Button(btn_frm, text="Cancel", command=on_cancel).pack(side="right")

        win.bind("<Return>", lambda e: on_ok())
        win.bind("<Escape>", lambda e: on_cancel())
        spin.focus_set()

    def set_layout_sort_case(self, value: bool) -> None:
        """Preferences: case-sensitive sorting in xlayout tabs (re-sorts
        the open ones right away)."""
        if bool(get_preference(PREF_LAYOUT_SORT_CASE, True)) == value:
            return
        set_preference(PREF_LAYOUT_SORT_CASE, value)
        for t in self.tabs:
            view = getattr(getattr(t, "canvas", None), "_layout_view", None)
            if view is not None:
                view.refresh_all()

    # ------------------------------------------------------------------ Edit helpers
    def _text_event(self, sequence: str) -> None:
        tab = self.current_tab()
        if isinstance(tab, EditorTab):
            tab.text.event_generate(sequence)

    def undo(self) -> None:
        tab = self.current_tab()
        if isinstance(tab, EditorTab):
            if getattr(tab, "undo_hook", None):   # e.g. timing marks in an audio tab
                tab.undo_hook()
                return
            try:
                tab.text.edit_undo()
            except tk.TclError:
                pass

    def redo(self) -> None:
        tab = self.current_tab()
        if isinstance(tab, EditorTab):
            if getattr(tab, "redo_hook", None):
                tab.redo_hook()
                return
            try:
                tab.text.edit_redo()
            except tk.TclError:
                pass

    def find(self) -> None:
        tab = self.current_tab()
        if not isinstance(tab, EditorTab):
            return
        needle = simpledialog.askstring("Find", "Find:")
        if not needle:
            return
        start = tab.text.search(needle, "1.0", stopindex="end", nocase=True)
        if start:
            end = f"{start}+{len(needle)}c"
            tab.text.tag_remove("sel", "1.0", "end")
            tab.text.tag_add("sel", start, end)
            tab.text.mark_set("insert", end)
            tab.text.see(start)
        else:
            messagebox.showinfo("Find", "Text not found.")

    def replace(self) -> None:
        # Simple sequential replace dialog
        tab = self.current_tab()
        if not isinstance(tab, EditorTab):
            return
        find_str = simpledialog.askstring("Replace", "Find:")
        if find_str is None:
            return
        repl_str = simpledialog.askstring("Replace", "Replace with:")
        if repl_str is None:
            return
        content = tab.get_content()
        new_content = content.replace(find_str, repl_str)
        if new_content != content:
            tab.text.delete("1.0", "end")
            tab.text.insert("1.0", new_content)
            tab.dirty = True
            tab.update_tab_label()
            self._update_title()
            messagebox.showinfo("Replace", "Replacement done.")
        else:
            messagebox.showinfo("Replace", "No occurrences found.")

    # ------------------------------------------------------------------ Help
    def show_shortcuts(self) -> None:
        """Help > Keyboard Shortcuts (F1): the cheat sheet in a window."""
        win = getattr(self, "_shortcuts_win", None)
        try:
            if win is not None and win.winfo_exists():
                win.lift()
                return
        except tk.TclError:
            pass
        win = self._shortcuts_win = tk.Toplevel(self)
        win.title("Keyboard Shortcuts")
        win.configure(bg="#ffffff")
        text = tk.Text(win, width=92, height=34, wrap="word", bg="#ffffff", fg="#1e1e1e", relief="flat",
                       padx=12, pady=8, font=("TkDefaultFont", 10))
        bar = ttk.Scrollbar(win, orient="vertical", command=text.yview)
        text.configure(yscrollcommand=bar.set)
        bar.pack(side="right", fill="y")
        text.pack(side="left", fill="both", expand=True)
        text.tag_configure("head", font=("TkDefaultFont", 11, "bold"), spacing1=8, spacing3=2, foreground="#0b5394")
        text.tag_configure("key", font=("TkFixedFont", 10, "bold"))
        for section, rows in SHORTCUTS:
            text.insert("end", section + "\n", "head")
            for keys, what in rows:
                text.insert("end", f"  {keys:<26}", "key")
                text.insert("end", what + "\n")
        text.configure(state="disabled")
        win.bind("<Escape>", lambda e: win.destroy())

    def show_about(self) -> None:
        extra = ""
        if not HAS_DND:
            extra = "\n\n(Drag-and-drop support: install tkinterdnd2)"
        if get_debug_level() > 0:
            extra += f"\n\nDebug level: {get_debug_level()}"
        messagebox.showinfo("About", about_text() + extra)

    def _in_background(self, work, done) -> None:
        """Run work() in a thread; done(result, error) on the Tk thread."""
        box = {}

        def run():
            try:
                box["result"] = work()
            except Exception as exc:
                box["error"] = exc
            box["done"] = True
        threading.Thread(target=run, daemon=True).start()

        def poll():
            if box.get("done"):
                done(box.get("result"), box.get("error"))
            else:
                self.after(150, poll)
        self.after(150, poll)

    def check_updates(self) -> None:
        """Help > Check for Updates: compare VERSION with the GitHub
        repository's (Preferences: owner/name); if newer, offer to update
        the program files, then to restart."""
        import updater
        repo = updater.default_repo(str(get_preference("update_repo", "") or ""), str(Path(__file__).resolve().parent))
        if not updater.valid_repo(repo):
            repo = simpledialog.askstring(
                "Check for Updates", "GitHub repository to update from (owner/name, e.g. someone/trackED):",
                parent=self) or ""
            repo = repo.strip().replace("https://github.com/", "").strip("/")
            if not updater.valid_repo(repo):
                return
            set_preference("update_repo", repo)
        branch = str(get_preference("update_branch", "") or updater.UPDATE_BRANCH)
        self.set_status(f"Checking {repo} for updates...")

        def got_version(remote, error):
            if error is not None:
                self.set_status("Update check failed")
                messagebox.showerror("Check for Updates", f"Couldn't read the version from {repo} ({branch}):\n"
                                                          f"{error}", parent=self)
                return
            if not updater.is_newer(remote, VERSION):
                self.set_status(f"{APP_NAME} {VERSION} is up to date")
                messagebox.showinfo("Check for Updates", f"You have the latest version ({VERSION}).", parent=self)
                return
            if not messagebox.askyesno(
                    "Check for Updates", f"Version {remote} is available (you have {VERSION}).\n\n"
                                         f"Update the program files from {repo} now?\n"
                                         "(The files it replaces are backed up in ~/.tracked first.)", parent=self):
                return
            self.set_status(f"Downloading {APP_NAME} {remote}...")
            app_dir = str(Path(__file__).resolve().parent)
            self._in_background(lambda: updater.apply_zip(updater.download(repo, branch), app_dir),
                                lambda res, err: applied(remote, res, err))

        def applied(remote, result, error):
            if error is not None:
                self.set_status("Update failed")
                messagebox.showerror("Check for Updates", f"The update failed:\n{error}", parent=self)
                return
            changed, backup = result
            self.set_status(f"Updated to {remote}: {len(changed)} file(s)")
            debug(1, f"{{green}}Updated {len(changed)} file(s) to {remote}; backup: {backup}")
            if not changed:
                messagebox.showinfo("Check for Updates", "All files were already up to date.", parent=self)
                return
            msg = (f"Updated {len(changed)} file(s) to version {remote}." +
                   (f"\nPrevious files: {backup}" if backup else ""))
            if updater.needs_restart(changed):
                if messagebox.askyesno("Check for Updates", msg + "\n\nRestart trackED now to use them?",
                                       parent=self):
                    self.restart()
            else:
                messagebox.showinfo("Check for Updates", msg, parent=self)
        self._in_background(lambda: updater.remote_version(repo, branch), got_version)

    def open_docs(self) -> None:
        webbrowser.open(documentation_url())

    # ------------------------------------------------------------------ Quit / session
    def _collect_session(self, active=None) -> dict:
        """active: the tab to reopen as the current one (default: the one
        selected now)."""
        open_files = []
        active_index = 0
        cur = active if active is not None else self.current_tab()
        idx = 0
        for t in self.tabs:
            if isinstance(t, EditorTab) and t.filepath:
                if t is cur:
                    active_index = idx
                open_files.append(t.filepath)
                t.save_current_sash()
                t.save_cursor_state()
                idx += 1
        data = load_session_data()
        data["open_files"] = open_files
        data["active_index"] = active_index
        data["recent"] = load_recent()
        return data

    def restart(self) -> None:
        """Save (asking about unsaved changes as for Quit), close, and start
        trackED again -- e.g. after the Install button added packages,
        which only a fresh Python process picks up. The open files come
        back through the saved session."""
        self._restart_requested = True
        self.on_quit()

    def _quit_cancelled(self) -> None:
        """The user stayed (Cancel in a close question): a later Ctrl+C
        asks again rather than exiting at once."""
        self._restart_requested = False
        guard = getattr(self, "_interrupt_guard", None)
        if guard is not None:
            guard.reset()

    def on_quit(self) -> None:
        # The tab the user was on: the questions below select other tabs
        # (to show which file they're about), which mustn't change what
        # the next start reopens as the current tab.
        active = self.current_tab()
        # Ask about every dirty tab
        for tab in list(self.tabs):
            hook = getattr(tab, "before_close_hook", None)
            if callable(hook):
                if isinstance(tab, EditorTab):
                    self.notebook.select(tab.frame)
                if not hook():
                    self._quit_cancelled()
                    return
            if isinstance(tab, EditorTab) and tab.dirty:
                self.notebook.select(tab.frame)
                name = abbreviated_name(tab.filepath)
                answer = messagebox.askyesnocancel(
                    "Unsaved Changes",
                    f'"{name}" has unsaved changes.\nSave before quitting?',
                )
                if answer is None:
                    self._quit_cancelled()
                    return
                if answer:
                    if not self.save_file():
                        self._quit_cancelled()
                        return
            # Persist sash even for clean tabs
            if isinstance(tab, EditorTab):
                tab.save_current_sash()
                tab.save_cursor_state()

        # Remember open files for next launch
        self._save_window_geometry()
        save_session_data(self._collect_session(active=active))
        debug(1, "{{pink}}Session saved, exiting")
        self._teardown_and_destroy()

    def _teardown_and_destroy(self) -> None:
        """Take the window down quickly: hide it first (no repaints of a
        half-destroyed window), let each plugin drop its widgets in one go
        (tab.teardown_hook -- e.g. a timing track's hundreds of card
        widgets, which Tk would otherwise remove one by one, re-laying out
        the text each time), then destroy. Each step's time goes to the
        debug log."""
        t0 = time.monotonic()
        try:
            self.withdraw()
        except tk.TclError:
            pass
        for tab in list(self.tabs):
            hook = getattr(tab, "teardown_hook", None)
            if callable(hook):
                t1 = time.monotonic()
                try:
                    hook()
                except Exception as exc:
                    debug(1, f"{{red}}teardown {getattr(tab, 'filepath', '?')}: {exc}")
                debug(2, f"quit: teardown {abbreviated_name(tab.filepath)} {1000 * (time.monotonic() - t1):.0f} ms")
        t1 = time.monotonic()
        # One Tk call for the whole window tree (tkinter's destroy() would
        # take every widget down separately -- seconds of X-server work).
        try:
            utils.fast_destroy(self)
            import tkinter
            if getattr(tkinter, "_default_root", None) is self:
                tkinter._default_root = None
        except Exception:
            self.destroy()
        debug(2, f"quit: destroy {1000 * (time.monotonic() - t1):.0f} ms, total {1000 * (time.monotonic() - t0):.0f} ms")


# Help > Keyboard Shortcuts. Keep in step with the bindings (and the
# tooltips that mention them): menus here, waveform_tab.py, timing_panel.py
# (TimingPanel.KEY_HELP), image_tab.py.
SHORTCUTS = [
    ("Files and editing (menus)", [
        ("Ctrl+N / Ctrl+O", "new tab / open a file"),
        ("Ctrl+S / Ctrl+Shift+S", "save / save as"),
        ("Ctrl+W", "close the tab"),
        ("Ctrl+Z / Ctrl+Y", "undo / redo (marks too, in an audio tab)"),
        ("Ctrl+X / Ctrl+C / Ctrl+V", "cut / copy / paste (text; marks when the waveform has the focus)"),
        ("Ctrl+F / Ctrl+H", "find / replace"),
        ("F1", "this list"),
    ]),
    ("Waveform (point at it to give it the focus)", [
        ("click / Ctrl+click", "move the @cursor (Ctrl+click on a mark in a track: select it too)"),
        ("drag", "new range;  Shift+click: range from the @cursor to here"),
        ("M  or  double-click", "new point mark at the @cursor / there"),
        ("Tab / Shift+Tab", "select the next / previous mark"),
        ("Home / End", "first / last mark of the track"),
        ("Up / Down", "move the selection between tracks"),
        ("Left / Right", "nudge the selected mark by one grid step"),
        ("Delete / Backspace", "delete the selected mark(s)"),
        ("Escape", "clear the selection"),
        ("Shift+click / Ctrl+click", "in a track band: select a run / add or remove one mark"),
        ("Ctrl+C / Ctrl+X / Ctrl+V", "copy / cut / paste marks (paste into the selected track, same times)"),
        ("mouse wheel", "zoom"),
    ]),
    ("Playback", [
        ("Play", "play from the @cursor / pause"),
        ("Play while paused", "start again from where Play started (or from a moved @cursor)"),
        ("Ctrl+Play", "resume from the paused spot"),
        ("Shift+Play", "loop"),
        ("\u25c0\u25c0 / \u25b6\u25b6", "5 s;  Shift: stem region edge;  Ctrl: start / end of the audio"),
    ]),
    ("Timing cards (in a card's text or time fields)", [
        ("Enter", "keep the text and go to the next card"),
        ("Shift+Enter", "a line break in the text"),
        ("Ctrl+Enter", "split the card at the text cursor"),
        ("Backspace at the start", "merge with the previous card"),
        ("Delete at the end", "merge with the next card"),
        ("Tab / Shift+Tab", "same field of the next / previous card (wraps around in the track)"),
        ("Ctrl+Home / Ctrl+End", "same field of the first / last card"),
        ("Ctrl+Space", "play / pause / resume the card  (Ctrl+Shift+Space: loop)"),
        ("Ctrl+[ / Ctrl+]", "Start / End to the @cursor"),
        ("Alt+Up / Alt+Down", "one syllable more / less for the word at the text cursor"),
        ("Alt+Right / Alt+Left", "more / less time for that word"),
        ("Escape", "undo the typing in the field"),
        ("Up / Down, Home / End", "(card list focused, not a field) previous / next, first / last card"),
    ]),
    ("Image tab", [
        ("+ / - / 0 / 1", "zoom in / out / fit / 100%"),
        ("Left / Right", "previous / next singing-face image"),
        ("Ctrl+Z", "undo a pixel-editor stroke"),
        ("Escape", "leave the box / pixel tool"),
        ("right-click", "(pixel editor) pick the color under the pointer"),
        ("middle-drag", "pan (while a tool is on)"),
    ]),
]


class UserActionLog:
    """Preferences > "Log my keys, clicks and menu picks" (or -actions):
    every key press, mouse click / wheel and menu pick becomes an
    "ACTION ..." line in the debug log (level USER_ACTION_LEVEL), naming
    the widget it went to -- so the steps to a problem can be read back.
    Plain typing is gathered into one "typed '...'" line per field. The
    check for the setting is made per event, so turning it on or off in
    Preferences takes effect at once."""

    TYPING_FLUSH_MS = 1200

    def __init__(self, root):
        self.root = root
        self._typed = []
        self._typed_widget = None
        self._flush_id = None
        root.bind_all("<KeyPress>", self.on_key, add="+")
        root.bind_all("<ButtonPress>", self.on_button, add="+")
        root.bind_all("<MouseWheel>", self.on_wheel, add="+")
        root.bind_class("Menu", "<<MenuSelect>>", self.on_menu_select, add="+")
        root.bind_class("Menu", "<ButtonRelease-1>", self.on_menu_pick, add="+")
        root.bind_class("Menu", "<KeyPress-Return>", self.on_menu_pick, add="+")
        self._menu_label = ""

    @staticmethod
    def describe(widget) -> str:
        """"Button 'Save'", "Entry (…card.start)", "Canvas (…waveform)"."""
        try:
            cls = widget.winfo_class()
        except Exception:
            return str(widget)
        text = ""
        try:
            if cls in ("Button", "TButton", "Label", "TLabel", "Menubutton", "TMenubutton", "Checkbutton",
                       "TCheckbutton", "Radiobutton", "TRadiobutton"):
                text = str(widget.cget("text") or "")
        except Exception:
            pass
        path = str(widget)
        tail = ".".join(path.split(".")[-2:]) if path.count(".") > 1 else path
        return f"{cls} '{text}'" if text else f"{cls} ({tail})"

    @staticmethod
    def key_name(event) -> str:
        mods = []
        state = getattr(event, "state", 0) or 0
        if state & 0x0004:
            mods.append("Ctrl")
        if state & 0x0008 or state & 0x20000:
            mods.append("Alt")
        if state & 0x0001 and len(getattr(event, "keysym", "")) > 1:
            mods.append("Shift")
        return "+".join(mods + [getattr(event, "keysym", "?")])

    def _log(self, text):
        debug(USER_ACTION_LEVEL, "ACTION " + text)

    def _flush(self):
        self._flush_id = None
        if self._typed:
            self._log(f"typed {''.join(self._typed)!r} in {self.describe(self._typed_widget)}")
        self._typed, self._typed_widget = [], None

    def on_key(self, event):
        if not log_actions_on():
            return
        ch = getattr(event, "char", "")
        plain = ch and ch.isprintable() and not (getattr(event, "state", 0) & 0x000C)
        if plain:
            if self._typed_widget is not event.widget:
                self._flush()
                self._typed_widget = event.widget
            self._typed.append(ch)
            try:
                if self._flush_id is not None:
                    self.root.after_cancel(self._flush_id)
                self._flush_id = self.root.after(self.TYPING_FLUSH_MS, self._flush)
            except (tk.TclError, ValueError):
                pass
            return
        if event.keysym in ("Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R", "Meta_L", "Meta_R",
                            "Super_L", "Super_R", "Caps_Lock", "ISO_Level3_Shift"):
            return
        self._flush()
        self._log(f"key {self.key_name(event)} in {self.describe(event.widget)}")

    def on_button(self, event):
        if not log_actions_on():
            return
        self._flush()
        names = {1: "click", 2: "middle-click", 3: "right-click", 4: "wheel up", 5: "wheel down"}
        what = names.get(getattr(event, "num", 0), f"button {getattr(event, 'num', '?')}")
        mods = self.key_name(event).rsplit("+", 1)[0] if "+" in self.key_name(event) else ""
        where = f" at {event.x},{event.y}" if getattr(event, "widget", None) is not None \
            and self._is_canvas(event.widget) else ""
        self._log(f"{(mods + '+') if mods else ''}{what} on {self.describe(event.widget)}{where}")

    @staticmethod
    def _is_canvas(widget):
        try:
            return widget.winfo_class() == "Canvas"
        except Exception:
            return False

    def on_wheel(self, event):
        if not log_actions_on():
            return
        self._log(f"wheel {'up' if getattr(event, 'delta', 0) > 0 else 'down'} on {self.describe(event.widget)}")

    def on_menu_select(self, event):
        try:
            idx = event.widget.index("active")
            self._menu_label = event.widget.entrycget(idx, "label") if idx is not None else ""
        except Exception:
            self._menu_label = ""

    def on_menu_pick(self, event):
        if not log_actions_on() or not self._menu_label:
            return
        self._flush()
        self._log(f"menu pick '{self._menu_label}'")


def restart_command(argv: List[str]) -> List[str]:
    """The command that starts trackED again: the same Python and options,
    without file names and -fresh (the saved session reopens the files)."""
    script = str(Path(__file__).resolve())
    opts = []
    skip_next = False
    for i, arg in enumerate(argv[1:], start=1):
        if skip_next:
            skip_next = False
            continue
        if arg == "-fresh" or not arg.startswith("-"):
            continue
        opts.append(arg)
        if arg in ("-debug", "-debug-default") and i + 1 < len(argv) and argv[i + 1].isdigit():
            opts.append(argv[i + 1])
            skip_next = True
    return [sys.executable, script] + opts


def relaunch(argv: List[str]) -> None:
    """Replace this process with a fresh trackED (Windows: start a new
    one and exit -- os.execv there doesn't keep the console attached)."""
    cmd = restart_command(argv)
    sys.stdout.flush()
    sys.stderr.flush()
    if sys.platform.startswith("win"):
        import subprocess
        subprocess.Popen(cmd, close_fds=True)
        os._exit(0)
    os.execv(cmd[0], cmd)


def capture_output_if_windowless() -> Optional[str]:
    """Started with pythonw.exe (trackED.cmd), there's no console: Python's
    stdout/stderr are None and any error -- even one that stops trackED
    from starting -- vanishes. Send them to ~/.tracked/console.log instead
    (overwritten each start). Returns the log path when redirected."""
    if sys.stderr is not None and sys.stdout is not None:
        return None
    try:
        folder = Path.home() / ".tracked"
        folder.mkdir(parents=True, exist_ok=True)
        path = folder / "console.log"
        log = open(path, "w", encoding="utf-8", buffering=1, errors="replace")
        log.write(f"trackED {VERSION} started {datetime.datetime.now():%Y-%m-%d %H:%M:%S} "
                  f"with {sys.executable}\n")
        sys.stdout = sys.stdout or log
        sys.stderr = sys.stderr or log
        return str(path)
    except OSError:
        return None


def startup_check() -> int:
    """`tracked.py --check` (trackED.cmd --check): print what trackED
    needs and whether it's there, open and close a Tk window, and exit
    -- for when the app window doesn't appear."""
    import platform
    ok = True
    print(f"trackED {VERSION}")
    print(f"Python {platform.python_version()} at {sys.executable}  ({platform.platform()})")
    try:
        root = tk.Tk()
        print(f"  ok       tkinter (Tk {root.tk.call('info', 'patchlevel')})")
        root.destroy()
    except Exception as exc:
        ok = False
        print(f"  FAILED   tkinter / Tk window: {exc}")
    try:
        import deps
        deps.main(["deps.py", "--list"])
    except Exception as exc:
        print(f"  FAILED   deps list: {exc}")
    for mod in ("editor_tab", "waveform_tab", "timing_panel", "image_tab", "xlayout_tab", "logview_tab"):
        try:
            __import__(mod)
            print(f"  ok       {mod}.py loads")
        except Exception as exc:
            ok = False
            print(f"  FAILED   {mod}.py: {exc!r}")
    log = Path.home() / ".tracked" / "console.log"
    if log.exists():
        print(f"\nLast windowless start's log ({log}):")
        print("".join(log.read_text(encoding="utf-8", errors="replace").splitlines(keepends=True)[-25:]))
    print("\nAll checks passed." if ok else "\nSome checks FAILED (see above).")
    return 0 if ok else 1


def parse_args(argv: List[str]):
    """Return (files, fresh, debug_level). debug_level is None when the
    command line doesn't set one (use the stored preference). The
    -debug-default option updates that stored preference as a side
    effect (and is then used for this run too)."""
    fresh = False
    debug_level: Optional[int] = None
    files = []
    i = 1
    while i < len(argv):
        arg = argv[i]
        if arg == "-fresh":
            fresh = True
        elif arg == "-busy":
            BUSY_REPORTS_CLI["on"] = True
        elif arg == "-actions":
            LOG_ACTIONS_CLI["on"] = True
        elif arg == "-nodebug":
            debug_level = 0
        elif arg == "-debug-default" or arg.startswith("-debug-default="):
            value: Optional[int] = None
            if "=" in arg:
                try:
                    value = int(arg.split("=", 1)[1])
                except ValueError:
                    value = None
            elif i + 1 < len(argv) and argv[i + 1].isdigit():
                value = int(argv[i + 1])
                i += 1
            stored = set_default_debug_level(value)   # None -> factory reset
            print(f"default debug level set to {stored}")
            if debug_level is None:
                debug_level = stored
        elif arg == "-debug":
            # next token may be the level
            if i + 1 < len(argv) and argv[i + 1].isdigit():
                debug_level = int(argv[i + 1])
                i += 1
            else:
                debug_level = 1
        elif arg.startswith("-debug="):
            try:
                debug_level = int(arg.split("=", 1)[1])
            except ValueError:
                debug_level = 1
        elif not arg.startswith("-"):
            files.append(arg)
        i += 1
    return files, fresh, debug_level


class InterruptGuard:
    """Ctrl+C in the terminal: the first one is a normal close request (the
    app asks about unsaved changes, as for the window's close button); a
    second one exits at once.

    The second Ctrl+C works even if the GUI is stuck: a small thread
    watches the signal wake-up pipe, which the interpreter writes to as
    soon as the signal arrives -- before any Python code (which a stuck
    main thread wouldn't get to) runs. A periodic no-op timer keeps Tk's
    loop returning to Python, so the first Ctrl+C is handled promptly.

    Also a stall watch: if the Tk loop doesn't come round for
    STALL_SECONDS, it prints the app's last steps (utils.crumb) with their
    times, and every thread's Python stack, to the terminal -- and again
    every REPORT_EVERY seconds while it stays stuck, so it shows whether
    the app is still running Python callbacks (new steps) or Tk is stuck
    on its own (nothing new). While stuck, a single Ctrl+C exits.
    Busy-but-responding stretches get a lighter report (_busy_watch)."""

    STALL_SECONDS = 5
    REPORT_EVERY = 10

    def __init__(self, app):
        import os
        import signal
        import threading
        self.app = app
        self.count = 0
        self._lock = threading.Lock()
        try:
            r, w = os.pipe()
            os.set_blocking(w, False)
            signal.set_wakeup_fd(w)
            self._pipe = r
            signal.signal(signal.SIGINT, self._on_sigint)
            threading.Thread(target=self._watch, name="interrupt-guard", daemon=True).start()
        except (ValueError, OSError, AttributeError) as exc:     # not the main thread / no pipes
            debug(1, f"{{red}}Ctrl+C guard not installed: {exc}")
            return
        app._interrupt_guard = self
        self._beat = time.monotonic()
        self._stalled_since = None
        threading.Thread(target=self._stall_watch, name="stall-watch", daemon=True).start()
        self._tick()

    def reset(self):
        with self._lock:
            self.count = 0

    def _watch(self):
        import os
        import signal
        while True:
            try:
                data = os.read(self._pipe, 64)
            except OSError:
                return
            for byte in data:
                if byte == signal.SIGINT:
                    with self._lock:
                        self.count += 1
                        count = self.count
                    if count >= 2 or self._stalled_since is not None:
                        sys.stderr.write("\nCtrl+C while the GUI is stuck (or a second Ctrl+C): "
                                         "exiting without saving.\n")
                        sys.stderr.flush()
                        os._exit(130)

    def _on_sigint(self, signum, frame):
        # runs in the main thread once Python gets control
        sys.stderr.write("\nCtrl+C: closing (press Ctrl+C again to exit at once)\n")
        sys.stderr.flush()
        try:
            self.app.after(0, self.app.on_quit)
        except tk.TclError:
            pass

    def _tick(self):
        now = time.monotonic()
        # how late this tick came: the time the main loop spent busy
        self._busy = getattr(self, "_busy", 0.0) + max(0.0, now - getattr(self, "_beat", now) - 0.25)
        self._beat = now
        if self._stalled_since is not None:
            sys.stderr.write(f"trackED: responsive again after {self._beat - self._stalled_since:.1f} s\n")
            sys.stderr.flush()
            self._stalled_since = None
        try:
            self.app.after(250, self._tick)
        except tk.TclError:
            pass

    BUSY_WINDOW = 5.0
    BUSY_REPORT = 0.5          # report when the main loop was busy more than half the window

    def _busy_watch(self, now):
        """Busy but not stuck (e.g. CPU at 100% while the window still
        responds): every BUSY_WINDOW seconds, if the main loop was busy more
        than half that time, print which app steps ran how often. Opt-in
        (Preferences, or -busy); the stall report is always on."""
        if not busy_reports_on():
            self._busy_window_start = None
            return
        start = getattr(self, "_busy_window_start", None)
        if start is None:
            self._busy_window_start, self._busy_at_start = now, getattr(self, "_busy", 0.0)
            self._cpu_at_start, self._threads_at_start = time.process_time(), self._thread_cpu()
            return
        if now - start < self.BUSY_WINDOW:
            return
        busy = getattr(self, "_busy", 0.0) - self._busy_at_start
        cpu = time.process_time() - self._cpu_at_start
        threads_now = self._thread_cpu()
        threads_then = self._threads_at_start
        self._busy_window_start, self._busy_at_start = now, getattr(self, "_busy", 0.0)
        self._cpu_at_start, self._threads_at_start = time.process_time(), threads_now
        span = now - start
        if busy < self.BUSY_REPORT * span and cpu < 0.8 * span:
            return
        counts = {}
        for first, label, count, last in utils.recent_crumbs():
            if last >= start:
                key = re.sub(r"\d+", "#", label)
                counts[key] = counts.get(key, 0) + count
        top = sorted(counts.items(), key=lambda kv: -kv[1])[:12]
        lines = [f"\ntrackED: busy -- main loop {100 * busy / span:.0f}%, CPU {100 * cpu / span:.0f}% "
                 f"of the last {span:.0f} s (still responding)."]
        per_thread = sorted(((name, sec - threads_then.get(name, 0.0)) for name, sec in threads_now.items()),
                            key=lambda kv: -kv[1])
        if per_thread:
            lines.append("CPU by thread: " + ", ".join(f"{name} {sec:.1f} s" for name, sec in per_thread[:5]
                                                       if sec >= 0.05))
        lines.append("App steps in that time (# = a number):")
        lines += [f"  {n:6d}  {label}" for label, n in top] or ["  (none -- the main thread's time went to Tk itself)"]
        sys.stderr.write("\n".join(lines) + "\n")
        sys.stderr.flush()

    @staticmethod
    def _thread_cpu():
        """CPU seconds used so far by each of this process's threads, by
        thread name (Linux /proc; {} elsewhere)."""
        names = {getattr(t, "native_id", None): t.name for t in threading.enumerate()}
        out = {}
        try:
            tick = os.sysconf("SC_CLK_TCK")
            for tid in os.listdir("/proc/self/task"):
                with open(f"/proc/self/task/{tid}/stat") as f:
                    fields = f.read().rsplit(")", 1)[1].split()
                sec = (int(fields[11]) + int(fields[12])) / tick       # utime + stime
                name = names.get(int(tid)) or f"thread {tid}"
                out[name] = out.get(name, 0.0) + sec
        except (OSError, ValueError, IndexError, AttributeError):
            return {}
        return out

    def _stall_watch(self):
        import faulthandler
        last_report = 0.0
        while True:
            time.sleep(1.0)
            now = time.monotonic()
            try:
                self._busy_watch(now)
            except Exception:
                pass
            stalled = now - self._beat
            if stalled < self.STALL_SECONDS:
                continue
            if self._stalled_since is None:
                self._stalled_since = self._beat
            if now - last_report < self.REPORT_EVERY:
                continue
            last_report = now
            lines = [f"\ntrackED: the GUI has not responded for {stalled:.1f} s. Last app steps "
                     "(seconds before now, xN = repeated):"]
            for first, label, count, last in utils.recent_crumbs()[-40:]:
                rep_txt = f" x{count}" if count > 1 else ""
                lines.append(f"  -{now - last:7.2f}  {label}{rep_txt}")
            lines.append("Python stacks:")
            sys.stderr.write("\n".join(lines) + "\n")
            sys.stderr.flush()
            try:
                faulthandler.dump_traceback(file=sys.stderr, all_threads=True)
            except Exception:
                pass


def main() -> None:
    if "--check" in sys.argv:
        sys.exit(startup_check())
    log = capture_output_if_windowless()
    try:
        files, fresh, dbg = parse_args(sys.argv)
        app = EditorApp(files_to_open=files, fresh=fresh, debug_level=dbg)
    except Exception:
        import traceback
        traceback.print_exc()
        if log:                      # no console to show it: say where it went
            try:
                root = tk.Tk()
                root.withdraw()
                messagebox.showerror(APP_NAME, "trackED couldn't start.\n\nThe error is in:\n" + log
                                     + "\n\nFor more checks, run:  trackED.cmd --check")
                root.destroy()
            except Exception:
                pass
        raise
    InterruptGuard(app)
    app._action_log = UserActionLog(app)
    app.mainloop()
    if getattr(app, "_restart_requested", False):
        relaunch(sys.argv)


if __name__ == "__main__":
    main()

#eof
