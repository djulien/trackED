"""Renders the content of one file in a notebook tab.
Top: graphical panel (Canvas) – starts small
Bottom: text editor with line numbers
Horizontal sash is user-draggable; position remembered per file.
"""

from __future__ import annotations

import time
import tkinter as tk
from tkinter import ttk, messagebox
from pathlib import Path
from typing import Callable, Optional

from utils import (
    abbreviated_name, get_sash_pos, set_sash_pos, get_autosave_seconds,
    get_cursor_pos, set_cursor_pos, DEFAULT_SASH_POS,
    is_probably_text_file, file_meta_summary, run_onload_plugins,
)
from logview_tab import debug
#def debug(level: int, *args, **kwargs):
#    msg = ""
#    for i, arg in enumerate(args):
#        msg += str(arg) + " "
#    print(msg)
#    return args[-1]  #for inlining last arg

DIRTY_MARKER_COLOR = "#d0021b"
DIAL_FRAMES = 16          # auto-save dial animation steps
DIAL_EMPTY = "#f3c4c8"    # the part of the dial still to go
_dial_imgs = {}


def _autosave_dial(master, fraction: float):
    """A small red dial for an unsaved tab: the red wedge grows clockwise
    from 12 o'clock as auto-save approaches (full = saving now). Frames
    are drawn once per Tk interpreter; None if images can't be made."""
    import math
    key = str(master.winfo_toplevel()) if hasattr(master, "winfo_toplevel") else "default"
    frames = _dial_imgs.get(key)
    if frames is None:
        frames = []
        try:
            size, gap = 11, 3
            c = (size - 1) / 2.0
            for f in range(DIAL_FRAMES + 1):
                img = tk.PhotoImage(master=master, width=size + gap, height=size)
                limit = 2 * math.pi * f / DIAL_FRAMES
                for y in range(size):
                    for x in range(size):
                        dx, dy = x - c, y - c
                        r = math.hypot(dx, dy)
                        if r > c + 0.5:
                            continue
                        if r >= c - 0.6:
                            img.put(DIRTY_MARKER_COLOR, (x, y))          # rim
                            continue
                        ang = math.atan2(dx, -dy) % (2 * math.pi)       # 0 at 12 o'clock, clockwise
                        img.put(DIRTY_MARKER_COLOR if ang <= limit else DIAL_EMPTY, (x, y))
                frames.append(img)
        except (tk.TclError, TypeError, AttributeError):
            frames = []
        _dial_imgs[key] = frames
    if not frames:
        return None
    return frames[max(0, min(DIAL_FRAMES, int(round(fraction * DIAL_FRAMES))))]
_dirty_marker_img = {}


def _dirty_marker(master):
    """A small red asterisk image for unsaved tabs (created once per Tk
    interpreter; None if it can't be made)."""
    key = str(master.winfo_toplevel()) if hasattr(master, "winfo_toplevel") else "default"
    if key in _dirty_marker_img:
        return _dirty_marker_img[key]
    img = None
    try:
        size = 9
        img = tk.PhotoImage(master=master, width=size + 3, height=size)   # 3 px gap before the name
        c = size // 2
        for i in range(size):
            for x, y in ((c, i), (i, c), (i, i), (size - 1 - i, i)):   # |  -  \  /
                if abs(x - c) + abs(y - c) <= c + 1:
                    img.put(DIRTY_MARKER_COLOR, (x, y))
        for x, y in ((c - 1, c), (c + 1, c), (c, c - 1), (c, c + 1)):    # thicken the center
            img.put(DIRTY_MARKER_COLOR, (x, y))
    except (tk.TclError, TypeError, AttributeError):
        img = None
    _dirty_marker_img[key] = img
    return img


class EditorTab:
    """One tab containing a vertical PanedWindow:
       - upper pane  = graphical panel (Canvas)
       - lower pane  = text area with scrollbars
    """

    def __init__(
        self,
        notebook: ttk.Notebook,
        filepath: Optional[str] = None,
        on_modified: Optional[Callable[["EditorTab"], None]] = None,
        on_close_request: Optional[Callable[["EditorTab"], None]] = None,
    ):
        self.notebook = notebook
        self.filepath = filepath
        self.on_modified = on_modified
        self.on_close_request = on_close_request
        self.dirty = False
        self._loading = False  # suppress dirty flag while loading file
        self._sash_ready = False

        # outer Frame that becomes the notebook page
        self.frame = ttk.Frame(notebook)

        # Vertical paned window
        self.paned = ttk.Panedwindow(self.frame, orient=tk.VERTICAL)
        self.paned.pack(fill="both", expand=True)

        # ----- Upper graphical panel (small by default) -----
        self.top_frame = ttk.Frame(self.paned)
        self.canvas = tk.Canvas(
            self.top_frame,
            bg="#f0f0f0",
            highlightthickness=0,
            height=DEFAULT_SASH_POS,
        )
        self.canvas.pack(fill="both", expand=True)

        # Simple placeholder graphics (can be replaced later)
        self.canvas.create_text(
            8, 6,
            anchor="nw",
            text="Graphical panel",
            fill="#888888",
            font=("Segoe UI", 9),
        )
        # Draw a light grid so it is obvious this is a canvas
        def _draw_grid(event=None):
            self.canvas.delete("grid")
            w = max(self.canvas.winfo_width(), 1)
            h = max(self.canvas.winfo_height(), 1)
            for x in range(0, w, 16):
                self.canvas.create_line(x, 0, x, h, fill="#e8e8e8", tags="grid")
            for y in range(0, h, 16):
                self.canvas.create_line(0, y, w, y, fill="#e8e8e8", tags="grid")
        self.canvas.bind("<Configure>", _draw_grid)
        self.paned.add(self.top_frame, weight=0)

        # ----- Lower: line numbers + text -----
        self._has_selection = False
        self._saved_sel = None
        self.bottom_frame = ttk.Frame(self.paned)

        self.linenumbers = tk.Canvas(
            self.bottom_frame,
            width=40,
            highlightthickness=0,
            borderwidth=0,
            bg="#f5f5f5",
        )
        self.text = tk.Text(
            self.bottom_frame,
            wrap="none",
            undo=True,
            maxundo=-1,
            autoseparators=True,
            font=("Consolas", 11) if tk.TkVersion >= 8.6 else ("Courier", 11),
            exportselection=False,          # keep selection on this widget
            selectbackground="#264f78",     # visible on light & dark
            selectforeground="#ffffff",
            inactiveselectbackground="#264f78",  # still visible without focus (Tk 8.5+)
         )
        self.vsb = ttk.Scrollbar(self.bottom_frame, orient="vertical", command=self._on_scroll)
        self.hsb = ttk.Scrollbar(self.bottom_frame, orient="horizontal", command=self.text.xview)
        self.text.configure(yscrollcommand=self._on_text_yscroll, xscrollcommand=self.hsb.set)
        self.linenumbers.configure(yscrollcommand=lambda *a: None)

        self.linenumbers.grid(row=0, column=0, sticky="ns")
        self.text.grid(row=0, column=1, sticky="nsew")
        self.vsb.grid(row=0, column=2, sticky="ns")
        self.hsb.grid(row=1, column=1, sticky="ew")
        self.bottom_frame.rowconfigure(0, weight=1)
        self.bottom_frame.columnconfigure(1, weight=1)

        self.paned.add(self.bottom_frame, weight=1)

        # Restore sash position after the widget is mapped
        self.frame.after(30, self._restore_sash)
        # Remember sash whenever the user finishes dragging it
        self.paned.bind("<ButtonRelease-1>", self._on_sash_released)
        # Custom tab label: [name *] [red X]
        # Custom tab label area (name + dirty marker; close via menu / Ctrl+W / middle-click)
        # Custom tab label helpers (kept for compatibility)
        self.tab_frame = ttk.Frame(notebook)
        self.label = ttk.Label(self.tab_frame, text=self._label_text())
        self.label.pack(side="left", padx=(4, 2))

#        self.close_btn = tk.Label(
#            self.tab_frame,
#            text="✕",
#            fg="#c0392b",
#            cursor="hand2",
#            font=("", 9, "bold"),
#        )
#        self.close_btn.pack(side="left", padx=(0, 4))
#        self.close_btn.bind("<Button-1>", self._request_close)
#        # Also allow middle-click on the tab label area to close
#        self.tab_frame.bind("<Button-2>", self._request_close)
#        self.label.bind("<Button-2>", self._request_close)

#        notebook.add(self.frame, text="")  # text is managed by our custom label
#        notebook.tab(self.frame, text="")  # keep empty; we draw our own
        notebook.add(self.frame, text=self._label_text())

        # After the tab is added we can attach the custom label
        # (Tk requires the tab to exist first)
        self._attach_custom_tab()

        self.text.bind("<KeyRelease>", lambda e: self._update_line_numbers())
        self.text.bind("<ButtonRelease-1>", lambda e: self._update_line_numbers())
        self.text.bind("<Configure>", lambda e: self._update_line_numbers())
        self.text.bind("<<Modified>>", self._on_text_modified)
#        self.text.bind("<Control-s>", lambda e: None)  # handled by main
        # MouseWheel is platform-specific; after_idle catches scroll
        self.text.bind("<MouseWheel>", lambda e: self.frame.after_idle(self._update_line_numbers))
        self.text.bind("<Button-4>", lambda e: self.frame.after_idle(self._update_line_numbers))
        self.text.bind("<Button-5>", lambda e: self.frame.after_idle(self._update_line_numbers))

        # Register with notebook (close button comes from CustomNotebook style)
        notebook.add(self.frame, text=self._label_text())

        if filepath:
            self.load_file(filepath)
        else:
            self._update_line_numbers()
            debug(2, "Created new untitled tab")

    def _on_scroll(self, *args):
        self.text.yview(*args)
        self._update_line_numbers()

    def _on_text_yscroll(self, first, last):
        """The scrollbar follows at once; the line numbers are redrawn once
        per burst of scrolling (dragging the scrollbar sends many of these),
        not once per step."""
        self.vsb.set(first, last)
        if getattr(self, "_numbers_pending", None) is None:
            try:
                self._numbers_pending = self.text.after(15, self._numbers_after_scroll)
            except tk.TclError:
                self._update_line_numbers()

    def _numbers_after_scroll(self):
        self._numbers_pending = None
        self._update_line_numbers()

    def set_line_numbers_visible(self, visible: bool) -> None:
        """Show / hide the line-number gutter (the timing cards number
        themselves, and redrawing the gutter on every scroll is costly
        with cards in the lines)."""
        if bool(visible) == getattr(self, "_line_numbers_shown", True):
            return
        self._line_numbers_shown = bool(visible)
        try:
            if visible:
                self.linenumbers.grid()
                self._update_line_numbers()
            else:
                self.linenumbers.delete("all")
                self.linenumbers.grid_remove()
        except tk.TclError:
            pass

    def _update_line_numbers(self, event=None) -> None:
        """
        One number per logical line (not per wrapped screen row).
        Uses dlineinfo() so wrapped continuations do not get extra numbers.
        """
        if not getattr(self, "_line_numbers_shown", True):
            return
        try:
            from utils import crumb
            crumb("editor line numbers")
        except ImportError:
            pass
        self.linenumbers.delete("all")
        try:
            end_line = int(self.text.index("end-1c").split(".")[0])
        except Exception:
            end_line = 1
        if end_line < 1:
            return

        # Optional override: list of original line numbers (e.g. log filter)
        orig = getattr(self, "_gutter_orig_nums", None)
        # Optional per-line vertical offsets (line -> px from the line's
        # top) for lines much taller than text, e.g. timing-panel cards
        # embedded in the Text: the number then sits beside the card's
        # first row instead of floating in the middle of it.
        offsets = getattr(self, "gutter_offsets", None) or {}

        width = 40
        if orig:
            width = max(40, 8 + 8 * len(str(max(orig))))
        else:
            width = max(40, 8 + 8 * len(str(end_line)))
        self.linenumbers.configure(width=width)

        # Font metrics for vertical centering of the first display row of each line
        try:
            font = self.text.cget("font")
        except Exception:
            font = None

        # Only the lines in view (dlineinfo of every line is slow when the
        # lines hold embedded widgets, e.g. a few hundred timing cards).
        first, last = 1, end_line
        try:
            top = self.text.index("@0,0")
            bottom = self.text.index(f"@0,{self.text.winfo_height()}")
            first = max(1, int(str(top).split(".")[0]))
            last = min(end_line, int(str(bottom).split(".")[0]))
        except Exception:
            first, last = 1, end_line
        for logical in range(first, last + 1):
            idx = f"{logical}.0"
            info = self.text.dlineinfo(idx)
            if info is None:
                continue  # line not in view (or not yet mapped)
            x, y, w, h, baseline = info
            label = str(orig[logical - 1]) if orig and logical <= len(orig) else str(logical)
            self.linenumbers.create_text(
                width - 4,
                y + offsets[logical] if logical in offsets else y + h // 2,
                anchor="e",
                text=label,
                fill="#666666",
                font=font,
            )

    # ------------------------------------------------------------------ Sash / cursor
    def _restore_sash(self, attempt: int = 0) -> None:
        """Apply the saved (or plugin-preferred) sash position -- but only
        once the pane really has its size. A tab that isn't visible yet (or
        a window still being laid out) reports ~1px, and a sash set then is
        clamped and lost; so retry briefly, and otherwise apply it when the
        pane is first shown (<Map>). Until applied, nothing is saved back
        (see _on_sash_released), so an unshown tab can't overwrite the
        stored position with a bogus one."""
        try:
            height = self.paned.winfo_height()
            want = max(get_sash_pos(self.filepath, default=self._sash_hint("preferred_sash")),
                       self._sash_hint("min_sash") or 0)
            if height < want + 40:
                if attempt < 20:
                    self.frame.after(50, lambda: self._restore_sash(attempt + 1))
                elif not getattr(self, "_sash_map_bound", False):
                    self._sash_map_bound = True
                    self.paned.bind("<Map>", lambda e: self._restore_sash(0) if not self._sash_ready else None,
                                    add="+")
                return
        except tk.TclError:
            return
        try:
            # A plugin's onload() may set tab.preferred_sash (used when this
            # file has no saved position yet) and tab.min_sash (a floor, so
            # a panel with its own toolbars can't be restored too small to
            # show its content). Either may be an int or a zero-arg callable,
            # evaluated here -- i.e. after the plugin's widgets have been
            # laid out and have real requested sizes.
            preferred = self._sash_hint("preferred_sash")
            minimum = self._sash_hint("min_sash") or 0
            pos = max(get_sash_pos(self.filepath, default=preferred), minimum)
            # sashpos expects an absolute pixel value from the top of the paned window
            self.paned.sashpos(0, pos)
            self._sash_ready = True
            debug(11, f"{{blue}}Restored sash for {self.filepath or 'Untitled'} → {pos}px")
        except tk.TclError:
            pass

    def _sash_hint(self, name: str) -> Optional[int]:
        value = getattr(self, name, None)
        if callable(value):
            try:
                value = value()
            except Exception:
                value = None
        return int(value) if value else None

    def _on_sash_released(self, event=None) -> None:
        if not self._sash_ready:
            return
        try:
            if not self.paned.winfo_ismapped() or self.paned.winfo_height() <= 1:
                return  # hidden tab: its sash reading would be meaningless
            pos = self.paned.sashpos(0)
            set_sash_pos(self.filepath, pos)
            debug(3, f"{{blue}}Saved sash {pos}px for {self.filepath or 'Untitled'}")
        except tk.TclError:
            pass

    def save_current_sash(self) -> None:
        """Call before the tab is destroyed so the latest position is stored."""
        self._on_sash_released()

    # ------------------------------------------------------------------ Cursor / view
    def save_cursor_state(self) -> None:
        if not self.filepath:
            return
        try:
            index = self.text.index("insert")
            yview = self.text.yview()[0]
            set_cursor_pos(self.filepath, index, yview)
            debug(4, f"{{blue}}Saved cursor {index} yview={yview:.3f} for {self.filepath}")
        except tk.TclError:
            pass

    def restore_cursor_state(self) -> None:
        if not self.filepath:
            return
        info = get_cursor_pos(self.filepath)
        try:
            self.text.mark_set("insert", info.get("index", "1.0"))
            self.text.see("insert")
            self.text.yview_moveto(float(info.get("yview", 0.0)))
            debug(11, f"{{blue}}Restored cursor for {self.filepath}")
        except (tk.TclError, ValueError):
            pass

    def save_selection_state(self) -> None:
        """Called when the user leaves this tab."""
        try:
            start = self.text.index("sel.first")
            end = self.text.index("sel.last")
            self._saved_sel = (start, end)
            self._has_selection = True
        except tk.TclError:
            self._saved_sel = None
            self._has_selection = False

    def restore_selection_state(self) -> None:
        """Called when the user returns to this tab."""
        if self._saved_sel:
            try:
                self.text.tag_remove("sel", "1.0", "end")
                self.text.tag_add("sel", self._saved_sel[0], self._saved_sel[1])
                self.text.mark_set("insert", self._saved_sel[1])
                self.text.see(self._saved_sel[0])
                self._has_selection = True
            except tk.TclError:
                self._saved_sel = None
                self._has_selection = False
        else:
            self._scroll_to_end_if_allowed()

    def _scroll_to_end_if_allowed(self) -> None:
        if not self._has_selection:
            self.text.see("end")

    def insert_styled(self, content: str, index: str = "end") -> None:
        from utils import insert_styled_text
        insert_styled_text(self.text, content, index)

    # ------------------------------------------------------------------ Tab label
    def _attach_custom_tab(self) -> None:
        """Replace the default tab text with our Frame containing label + close button."""
        try:
#?            self.notebook.tab(self.frame, compound="left")
            # The only reliable way in pure Tk is to set the tab text to empty
            # and use a separate label that we position... but Notebook does not
            # easily support arbitrary widgets as tab labels in all versions.
            # Workaround used by many pure-Tk editors: keep a short text and
            # put the close button next to it via a style, OR simply use the
            # text and a close accelerator.  For a clean "red X on the tab"
            # we keep the custom frame approach that works on both Linux/Windows
            # with recent Tk.
            self.notebook.tab(self.frame, text=self._label_text())
            # Store reference so we can update later
        except tk.TclError:
            pass

    def _label_text(self) -> str:
        name = abbreviated_name(self.filepath)
        return f"{'*' if self.dirty else ''}{name}"

    def update_tab_label(self, autosave_fraction: Optional[float] = None) -> None:
        """Unsaved changes: a red marker in front of the name -- an
        auto-save countdown dial that fills as the save approaches (or a
        red asterisk when auto-save is off). ttk.Notebook can't color one
        tab's text, but each tab can carry its own image; the plain-text
        "*" is the fallback if images fail."""
        name = abbreviated_name(self.filepath)
        try:
            img = None
            if self.dirty:
                if autosave_fraction is None:
                    autosave_fraction = self._autosave_fraction()
                if autosave_fraction is not None:
                    img = _autosave_dial(self.notebook, autosave_fraction)
                if img is None:
                    img = _dirty_marker(self.notebook)
            if img is not None:
                self.notebook.tab(self.frame, text=name, image=img, compound="left")
            else:
                self.notebook.tab(self.frame, text=self._label_text(), image="")
        except tk.TclError:
            pass

    def _on_text_modified(self, event=None) -> None:
        if self._loading or getattr(self, "protect_file", False):
            self.text.edit_modified(False)
            return
        if self.text.edit_modified():
            if not self.dirty:
                self.dirty = True
                self.dirty_since = time.monotonic()   # auto-save counts from here
                self.update_tab_label()
                if self.on_modified:
                    self.on_modified(self)
            self.text.edit_modified(False)
            self._update_line_numbers()

    def _request_close(self) -> None:
        if self.on_close_request:
            self.on_close_request(self)

    # ------------------------------------------------------------------ File I/O with plugins
    def load_file(self, path: str) -> bool:
        path = str(Path(path).resolve())
        self.filepath = path
        self._loading = True
        self.text.delete("1.0", "end")

        # Clear previous plugin drawing on the canvas
        self._plugin_image = None
        try:
            self.canvas.delete("plugin_image")
            for child in self.canvas.winfo_children():
                child.destroy()
        except tk.TclError:
            pass
        # ...and any toolbars a plugin packed beside the canvas (in its
        # parent frame), e.g. image_tab's zoom bar or waveform_tab's rows.
        for attr in ("_plugin_toolbars", "_waveform_toolbars"):
            for w in getattr(self.canvas, attr, None) or []:
                try:
                    w.destroy()
                except tk.TclError:
                    pass
            setattr(self.canvas, attr, [])

        # Stop a previous plugin poll timer if any
        if getattr(self, "_plugin_after_id", None) is not None:
            try:
                self.frame.after_cancel(self._plugin_after_id)
            except Exception:
                pass
            self._plugin_after_id = None

        # Panel-size hints belong to whichever plugin claims *this* load
        self.preferred_sash = None
        self.min_sash = None
        self._sash_ready = False   # re-applied (and only then saved) for the new file
        # A plugin sets this when the text panel is only a view of a
        # binary file (e.g. audio): its text must never be saved over it.
        self.protect_file = False
        # A plugin can route Edit > Undo/Redo (and Ctrl+Z/Ctrl+Y in the text
        # panel) to its own history, e.g. waveform_tab's timing marks.
        self.undo_hook = None
        self.redo_hook = None
        self.gutter_offsets = None
        # save_hook: a plugin's own save for files whose changes live
        # elsewhere (waveform_tab saves marks to the sidecar cache, never
        # the audio). title_detail: extra text for the window title, e.g.
        # the audio duration.
        self.save_hook = None
        self.title_detail = None
        # before_close_hook: a plugin's last question before the tab/app
        # closes; returns False to cancel the close.
        self.before_close_hook = None
        # teardown_hook: called once when the app is quitting, after all
        # questions/saves, to drop a plugin's widgets fast (see tracked.py)
        self.teardown_hook = None
        try:
            self.text.configure(state="normal", undo=True)
        except tk.TclError:
            pass

        claimed = run_onload_plugins(
            path, canvas=self.canvas, text=self.text, tab=self
        )

        if not claimed:
            from utils import insert_styled_text
            if is_probably_text_file(path):
                try:
                    data = Path(path).read_text(encoding="utf-8", errors="replace")
                    self.text.delete("1.0", "end")
                    insert_styled_text(self.text, data)  #When loading plain text (non-plugin), use styled insert
                    debug(1, f"{{blue}}Opened text file {path}")
                except Exception as e:
                    messagebox.showerror("Open Error", f"Could not open file:\n{e}")
                    debug(1, f"Failed to open {path}: {e}")
                    self._loading = False
                    return False
            else:
                data = file_meta_summary(path)
                self.text.delete("1.0", "end")
                insert_styled_text(self.text, data)  #allow styled
                debug(1, f"{{yellow}}Opened binary/non-text as summary: {path}")

        self.text.edit_modified(False)
        self.text.edit_reset()
        self._loading = False
        self.dirty = False
        self.update_tab_label()
        self._update_line_numbers()
        self.frame.after(40, self._restore_sash)
        self.frame.after(50, self.restore_cursor_state)
        return True

    def OLD_load_file(self, path: str) -> bool:
        path = str(Path(path).resolve())
        self.filepath = path
        self._loading = True
        self.text.delete("1.0", "end")

        # Clear any previous plugin image reference
        self._plugin_image = None
        try:
            self.canvas.delete("plugin_image")
        except tk.TclError:
            pass

        # 1. Plugin onload() hooks from *_tab.py
        plugin_content = run_onload_plugins(path)
        if plugin_content is not None:
            self.text.insert("1.0", plugin_content)
            debug(1, f"Plugin handled {path}")
        elif is_probably_text_file(path):
            try:
                data = Path(path).read_text(encoding="utf-8", errors="replace")
                self.text.insert("1.0", data)
                debug(1, f"Opened text file {path}")
            except Exception as e:
                messagebox.showerror("Open Error", f"Could not open file:\n{e}")
                debug(1, f"Failed to open {path}: {e}")
                self._loading = False
                return False
        else:
            # Non-text: show metadata only
            summary = file_meta_summary(path)
            self.text.insert("1.0", summary)
            debug(1, f"Opened binary/non-text as summary: {path}")

        self.text.edit_modified(False)
        self.text.edit_reset()  # clear undo stack
        self._loading = False
#        self.filepath = str(Path(path).resolve())
        self.dirty = False
        self.update_tab_label()
        # Apply the sash that belongs to this file
        self._update_line_numbers()
        self.frame.after(40, self._restore_sash)
        self.frame.after(50, self.restore_cursor_state)
        return True

    def get_content(self) -> str:
        return self.text.get("1.0", "end-1c")

    def apply_styles_to_text_widget(text: tk.Text) -> None:
        """Re-parse entire widget content and apply tags (keeps {markers} in buffer)."""
        ensure_style_tags(text)
        content = text.get("1.0", "end-1c")
        # clear old style tags
        for t in text.tag_names():
            if str(t).startswith("style_"):
                text.tag_remove(t, "1.0", "end")
        # walk line by line with absolute positions
        line_start = "1.0"
        for line in content.splitlines():
            line_end = text.index(f"{line_start} lineend")
            # map visible ranges: markers stay in buffer; tag ranges skip marker spans
            pos = 0
            color = bold = italic = underline = False
            # early timestamp color
            early = None
            mt = _TIMESTAMP_RE.match(line)
            if mt:
                rest = line[mt.end():]
                m2 = _STYLE_TAG_RE.match(rest)
                if m2 and m2.group(1).lower() in _LOG_COLORS:
                    early = m2.group(1).lower()
                    color = early
                    # tag timestamp range
                    a = text.index(f"{line_start}+{0}c")
                    b = text.index(f"{line_start}+{mt.end()}c")
                    for tg in _tags_for_state(early, False, False, False):
                        text.tag_add(tg, a, b)
            for m in _STYLE_TAG_RE.finditer(line):
                # style text between pos and m.start()
                if m.start() > pos:
                    a = text.index(f"{line_start}+{pos}c")
                    b = text.index(f"{line_start}+{m.start()}c")
                    for tg in _tags_for_state(color, bold, italic, underline):
                        text.tag_add(tg, a, b)
                name = m.group(1).lower()
                if name == "reset":
                    color = bold = italic = underline = False
                elif name in _LOG_COLORS:
                    color = name
                elif name == "bold":
                    bold = True
                elif name == "italic":
                    italic = True
                elif name == "underline":
                    underline = True
                pos = m.end()
            if pos < len(line):
                a = text.index(f"{line_start}+{pos}c")
                b = text.index(f"{line_start}+{len(line)}c")
                for tg in _tags_for_state(color, bold, italic, underline):
                    text.tag_add(tg, a, b)
            line_start = text.index(f"{line_start}+1l")

    def _autosave_fraction(self) -> Optional[float]:
        """0..1 of the way to this tab's auto-save, or None if off."""
        interval = get_autosave_seconds()
        since = getattr(self, "dirty_since", None)
        if interval <= 0 or since is None:
            return None
        return max(0.0, min(1.0, (time.monotonic() - since) / interval))

    def mark_dirty(self) -> None:
        """For plugin views whose edits aren't in the Text widget (e.g.
        timing marks): flag unsaved changes the same way text edits do."""
        if not self.dirty:
            self.dirty = True
            self.dirty_since = time.monotonic()   # auto-save counts from here
            self.update_tab_label()
        if self.on_modified:
            self.on_modified(self)

    def refresh_title(self) -> None:
        """Ask the app to redraw the window title (e.g. after a plugin set
        title_detail once its file finished loading)."""
        if self.on_modified:
            self.on_modified(self)

    def mark_clean(self) -> None:
        self.dirty = False
        self.dirty_since = None
        self.text.edit_modified(False)
        self.update_tab_label()

    def set_filepath(self, path: str) -> None:
        old = self.filepath
        self.filepath = str(Path(path).resolve())
        # Migrate sash position if the file was previously untitled or renamed
        if old != self.filepath:
            try:
                set_sash_pos(self.filepath, self.paned.sashpos(0))
            except tk.TclError:
                pass
        self.update_tab_label()
        debug(2, f"Path set to {self.filepath}")

    def focus(self) -> None:
        self.text.focus_set()

    def destroy(self) -> None:
        if getattr(self, "_plugin_after_id", None) is not None:
            try:
                self.frame.after_cancel(self._plugin_after_id)
            except Exception:
                pass
            self._plugin_after_id = None
        self.save_current_sash()
        self.save_cursor_state()
        try:
            self.notebook.forget(self.frame)
        except tk.TclError:
            pass
        self.frame.destroy()
        debug(2, f"Closed tab {self.filepath or 'Untitled'}")

#eof