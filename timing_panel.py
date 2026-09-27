"""
timing_panel.py -- the timing-track editor shown in an audio tab's text
panel (the lower pane) while a timing track, or a mark inside one, is
selected in waveform_tab.py.

One "card" per mark/range, in time order, embedded in the Text widget
(so it scrolls like the rest of the panel):

    #3  Start [0:12.340] [-][+][@]   End [0:13.100] [-][+][@]   [>] [Split] [Merge v]
        [ text of the mark ........................................ ]

  - Start/End accept m:ss.mmm, h:mm:ss.mmm or plain seconds; Enter or
    leaving the field applies it. Clearing End turns a range into a point;
    giving a point an End turns it into a range.
  - [-]/[+] nudge by the header's Step; [@] sets the time to the current
    playback position (or the Ctrl+click cursor when stopped).
  - The text field edits the mark's label.
  - Split: if the text cursor is inside the label, splits the text there
    and divides the range's time in proportion to each half's text;
    otherwise splits at the playback/cursor position if it falls inside
    the range, else at the middle word. See timing_helpers.plan_split.
  - Merge v: merges this mark with the next one in the track into one
    range (labels joined).

When nothing track-related is selected the panel shows the tab's normal
information text again. Not a *_tab.py file, so plugin discovery skips it.
"""

from __future__ import annotations

import tkinter as tk
from tkinter import ttk
from typing import Dict, List, Optional

from utils import insert_styled_text

import timing_helpers as th

STEP_CHOICES = ["0.01", "0.05", "0.1", "0.25", "0.5", "1.0"]

# Every classic-Tk widget here gets explicit colors: with a dark desktop
# theme, Tk's default foreground is light and disappears on these light
# backgrounds.
FG = "#1e1e1e"
FG_DIM = "#666666"
FG_DISABLED = "#a0a0a0"
HEADER_BG = "#ececec"
CARD_BG = "#f4f4f4"
CARD_SEL_BG = "#fff3b0"
CARD_BAD_BG = "#ffd6d6"
ENTRY_BG = "#ffffff"
BTN_BG = "#e2e2e2"
BTN_HOVER_BG = "#cfe0ff"
BTN_PRESS_BG = "#b3cdfa"
DELETE_FG = "#b00020"
FG_ON_DARK = "#ffffff"
NUDGE_REPEAT_DELAY_MS = 1000   # hold -/+ this long, then it auto-repeats
NUDGE_REPEAT_INTERVAL_MS = 80


SHIFT_MASK = 0x0001
PLAY_GLYPH, PAUSE_GLYPH = "\u25b6", "\u275a\u275a"


class _Tip:
    """Small delayed tooltip (explicit colors for dark desktop themes)."""

    def __init__(self, widget, text, delay_ms=500):
        self.widget, self.text, self.delay_ms = widget, text, delay_ms
        self._after = None
        self._tip = None
        widget.bind("<Enter>", self._schedule, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonPress>", self._hide, add="+")

    def _schedule(self, _e=None):
        self._after = self.widget.after(self.delay_ms, self._show)

    def _show(self):
        if self._tip is not None:
            return
        try:
            x = self.widget.winfo_rootx() + 10
            y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
            self._tip = tk.Toplevel(self.widget)
            self._tip.wm_overrideredirect(True)
            self._tip.wm_geometry(f"+{x}+{y}")
            tk.Label(self._tip, text=self.text, background="#ffffe0", foreground=FG, relief="solid",
                     borderwidth=1, font=("TkDefaultFont", 8), padx=4, pady=2).pack()
        except (tk.TclError, TypeError):
            self._tip = None

    def _hide(self, _e=None):
        if self._after is not None:
            try:
                self.widget.after_cancel(self._after)
            except Exception:
                pass
            self._after = None
        if self._tip is not None:
            try:
                self._tip.destroy()
            except Exception:
                pass
            self._tip = None


def contrast_fg(bg: str) -> str:
    """Dark or light text, whichever reads better on bg (#rrggbb)."""
    try:
        r, g, b = (int(bg.lstrip("#")[i:i + 2], 16) / 255.0 for i in (0, 2, 4))
    except (ValueError, IndexError):
        return FG
    return FG if (0.299 * r + 0.587 * g + 0.114 * b) > 0.55 else FG_ON_DARK


def _style_button(btn: tk.Button) -> tk.Button:
    """Visible at rest, highlighted + hand cursor on hover (bound
    explicitly, since tk.Button hover colors differ by platform)."""
    btn.configure(bg=BTN_BG, fg=FG, activebackground=BTN_PRESS_BG, activeforeground=FG,
                  disabledforeground=FG_DISABLED, relief="flat", overrelief="raised", bd=1,
                  highlightthickness=0, cursor="hand2", takefocus=0)

    def enter(_e):
        if str(btn.cget("state")) != "disabled":
            btn.configure(bg=BTN_HOVER_BG)

    btn.bind("<Enter>", enter, add="+")
    btn.bind("<Leave>", lambda _e: btn.configure(bg=BTN_BG), add="+")
    return btn


def _count(result) -> int:
    """tk.Text.count() returns a tuple, an int or None depending on the
    Tk/Python version."""
    if result is None:
        return 0
    if isinstance(result, (tuple, list)):
        return int(result[0]) if result else 0
    return int(result)


class WrapField:
    """The card's text field: a word-wrapping tk.Text that grows to fit
    its text (up to MAX_LINES), with the small Entry-like API the panel
    uses (get / delete(0, "end") / insert(0, s) / index("insert") /
    icursor / select_range / selected_span). Enter commits (Shift+Enter
    inserts a line break); anything else is passed through to the Text."""

    MAX_LINES = 8

    def __init__(self, parent):
        self.widget = tk.Text(parent, height=1, width=20, wrap="word", undo=False, font=("TkDefaultFont", 10),
                              bg=ENTRY_BG, fg=FG, insertbackground=FG, selectbackground="#264f78",
                              selectforeground="#ffffff", relief="solid", bd=1, highlightthickness=1,
                              highlightcolor="#7aa7e0", highlightbackground="#c8c8c8", padx=3, pady=2)
        self.widget.bind("<Configure>", lambda e: self.fit(), add="+")
        self.widget.bind("<KeyRelease>", lambda e: self.fit(), add="+")
        self.widget.bind("<Tab>", self._focus_next)

    def __getattr__(self, name):          # grid / bind / after / configure / fire ...
        return getattr(self.widget, name)

    def _focus_next(self, event=None):
        try:
            self.widget.tk_focusNext().focus_set()
        except (tk.TclError, AttributeError):
            pass
        return "break"

    def _pos(self, offset) -> str:
        return "end-1c" if offset == "end" else f"1.0 + {int(offset)} chars"

    def get(self) -> str:
        return self.widget.get("1.0", "end-1c")

    def delete(self, first=0, last="end") -> None:
        self.widget.delete("1.0", "end")

    def insert(self, index, text) -> None:
        self.widget.insert("end" if index == "end" else self._pos(index), text)
        self.fit()

    def index(self, which) -> int:
        if which == "insert":
            return _count(self.widget.count("1.0", "insert", "chars"))
        return len(self.get())

    def icursor(self, offset) -> None:
        self.widget.mark_set("insert", self._pos(offset))

    def select_range(self, first, last) -> None:
        self.widget.tag_remove("sel", "1.0", "end")
        self.widget.tag_add("sel", self._pos(first), self._pos(last))

    def selected_span(self):
        """(start, end) character offsets of the selection, or None."""
        ranges = self.widget.tag_ranges("sel")
        if not ranges or len(ranges) < 2:
            return None
        a = _count(self.widget.count("1.0", ranges[0], "chars"))
        b = _count(self.widget.count("1.0", ranges[1], "chars"))
        return (a, b) if b > a else None

    def fit(self) -> None:
        """Height = number of wrapped display lines (1..MAX_LINES)."""
        try:
            lines = _count(self.widget.count("1.0", "end", "displaylines")) or 1
            lines = max(1, min(self.MAX_LINES, lines))
            if int(self.widget.cget("height") or 1) != lines:
                self.widget.configure(height=lines)
        except (tk.TclError, TypeError, ValueError):
            pass


def _style_entry(entry: tk.Entry) -> tk.Entry:
    entry.configure(bg=ENTRY_BG, fg=FG, insertbackground=FG, disabledforeground=FG_DISABLED,
                    selectbackground="#264f78", selectforeground="#ffffff",
                    relief="solid", bd=1, highlightthickness=1, highlightcolor="#7aa7e0",
                    highlightbackground="#c8c8c8")
    return entry


class TimingPanel:
    def __init__(self, controller, text: tk.Text):
        self.ctl = controller
        self.text = text
        self.mode = "info"            # "info" | "track"
        self.track_id: Optional[str] = None
        self.cards: Dict[str, Dict] = {}   # mark id -> widgets
        self.order: List[str] = []
        self.step_var = tk.StringVar(value="0.1")
        self.spacers: List[tk.Frame] = []
        self._header_label = None
        self._extras: List[tk.Widget] = []
        try:
            self.text.bind("<Configure>", self._on_text_configure, add="+")
            self.text.bind("<Button-1>", self._click_off, add="+")
        except tk.TclError:
            pass

    # ------------------------------------------------------------------ public
    def sync(self, force: bool = False) -> None:
        """Called after every waveform render: decide which view to show,
        and update it with as little churn as possible (entries being
        edited keep their contents and focus)."""
        track_id = self.ctl.panel_track_id()
        if track_id is None:
            if self.mode != "info" or force:
                self.show_info()
            return
        track = self.ctl.track_by_id(track_id)
        marks = self.ctl.track_marks(track_id)
        ids = [m["id"] for m in marks]
        if force or self.mode != "track" or track_id != self.track_id or ids != self.order:
            self._build(track, marks)
        else:
            self._update(track, marks)

    def show_info(self) -> None:
        self._clear()
        self.mode = "info"
        self.track_id = None
        self._with_text(lambda: insert_styled_text(self.text, self.ctl.info_text))
        self._refresh_gutter()

    def append_info(self, styled: str) -> None:
        """Info-mode text grows as analysis/transcription progress; only
        shown immediately if the info view is current."""
        if self.mode != "info":
            return
        def put():
            insert_styled_text(self.text, styled)
            self.text.see("end")
        self._with_text(put)

    # ------------------------------------------------------------------ building
    def _with_text(self, fn) -> None:
        """Rewrite the Text without marking the tab dirty (the tab holds an
        audio file; its text is never saved -- see tab.protect_file)."""
        tab = self.ctl.tab
        was_loading = getattr(tab, "_loading", False)
        if tab is not None:
            tab._loading = True
        try:
            self.text.configure(state="normal")
            fn()
            if self.mode == "track":
                self.text.configure(state="disabled")
            self.text.edit_modified(False)
        except tk.TclError:
            pass
        finally:
            if tab is not None:
                tab._loading = was_loading

    def _clear(self) -> None:
        for card in self.cards.values():
            try:
                card["frame"].destroy()
            except tk.TclError:
                pass
        for extra in getattr(self, "_extras", []):
            try:
                extra.destroy()
            except tk.TclError:
                pass
        self._extras = []
        self.cards = {}
        self.order = []
        self.spacers = []
        self._with_text(lambda: self.text.delete("1.0", "end"))

    def _build(self, track, marks) -> None:
        self._clear()
        self.mode = "track"
        self.track_id = track["id"] if track else None
        self.order = [m["id"] for m in marks]

        def fill():
            header = self._make_header(track, marks)
            self.text.insert("end", " ")
            self.text.window_create("end", window=header)
            self.text.insert("end", "\n")
            if not marks:
                insert_styled_text(self.text, "{yellow}  (no marks in this track yet -- drag marks "
                                              "from the waveform into its band)\n")
            for i, m in enumerate(marks):
                card = self._make_card(i, m, is_last=(i == len(marks) - 1))
                self.cards[m["id"]] = card
                self.text.insert("end", " ")
                self.text.window_create("end", window=card["frame"])
                self.text.insert("end", "\n")
        self._with_text(fill)
        self._on_text_configure()
        self._update(track, marks, force=True)
        self._scroll_to_selected()
        self._refresh_gutter()

    def _make_header(self, track, marks):
        frame = tk.Frame(self.text, bg=HEADER_BG, padx=6, pady=3)
        self._extras.append(frame)
        name = track["name"] if track else "?"
        swatch = tk.Frame(frame, width=12, height=12, bg=(track or {}).get("color", "#888888"))
        swatch.pack(side="left", padx=(0, 6))
        self._header_label = tk.Label(frame, text=f"Track: {name}   ({len(marks)} marks)",
                                      font=("TkDefaultFont", 10, "bold"), bg=HEADER_BG, fg=FG)
        self._header_label.pack(side="left")
        tk.Label(frame, text="   Step (s):", bg=HEADER_BG, fg=FG).pack(side="left")
        combo = ttk.Combobox(frame, textvariable=self.step_var, values=STEP_CHOICES, width=5)
        combo.pack(side="left", padx=(2, 10))
        hint = tk.Label(frame, text="Ctrl+click the waveform to place @cursor and Split",
                        fg=FG_DIM, bg=HEADER_BG)
        hint.pack(side="left")
        # Clicking the header's background also "clicks off" the cards.
        for widget in (frame, swatch, self._header_label, hint):
            widget.bind("<Button-1>", self._click_off, add="+")
        self._forward_wheel(frame)
        return frame

    def _make_card(self, index, mark, is_last):
        normal_bg = self._card_bg(selected=False)
        f = tk.Frame(self.text, bg=normal_bg, bd=1, relief="groove", padx=4, pady=3)
        w: Dict = {"frame": f, "id": mark["id"]}
        col = 0

        def small_btn(text, cmd):
            return _style_button(tk.Button(f, text=text, command=cmd, padx=2, pady=0, width=2))

        w["num"] = tk.Label(f, text=f"#{index + 1}", width=4, anchor="w", bg=normal_bg,
                            fg=contrast_fg(normal_bg), font=("TkDefaultFont", 9, "bold"))
        w["labels"] = [w["num"]]   # recolored with the card on selection
        w["num"].grid(row=0, column=col); col += 1

        # Play/Pause (+ Stop, shown only while this mark is paused) on the left.
        play = _style_button(tk.Button(f, text=PLAY_GLYPH, width=2, padx=4, pady=0,
                                       command=lambda mid=mark["id"]: self._toggle_play(mid)))
        play.grid(row=0, column=col, padx=(2, 1)); col += 1
        w["play"] = play
        play._loop_hover = True   # waveform_tab's Shift key handler updates its cursor too
        # Shift+click loops this card's span (like the main Play button);
        # the pointer shows the loop cursor while Shift is held over it.
        play.bind("<ButtonRelease-1>",
                  lambda ev: setattr(self, "_shift_on_play", bool(ev.state & SHIFT_MASK)), add="+")
        for seq in ("<Enter>", "<Motion>"):
            play.bind(seq, lambda ev, b=play: b.configure(cursor="exchange" if ev.state & SHIFT_MASK
                                                           else "hand2"), add="+")
        _Tip(play, "Play / pause this mark\nShift+click: loop it until stopped")
        stop = _style_button(tk.Button(f, text="\u25a0", width=2, padx=4, pady=0,
                                       command=lambda: self.ctl.stop_play()))
        stop.grid(row=0, column=col, padx=(1, 2))
        stop.grid_remove()          # only while paused (see _update)
        col += 1
        w["stop"] = stop
        _Tip(stop, "Reset: back to where Play started")

        for which in ("start", "end"):
            lbl = tk.Label(f, text=which.capitalize(), bg=normal_bg, fg=contrast_fg(normal_bg))
            lbl.grid(row=0, column=col, padx=(6, 2)); col += 1
            w["labels"].append(lbl)
            e = _style_entry(tk.Entry(f, width=11, justify="right"))
            e.grid(row=0, column=col); col += 1
            e.bind("<Return>", lambda ev, mid=mark["id"], wh=which: self._commit_time(mid, wh))
            e.bind("<KP_Enter>", lambda ev, mid=mark["id"], wh=which: self._commit_time(mid, wh))
            e.bind("<FocusOut>", lambda ev, mid=mark["id"], wh=which: self._commit_time(mid, wh))
            e.bind("<Escape>", lambda ev, mid=mark["id"]: self._revert(mid))
            e.bind("<FocusIn>", lambda ev, mid=mark["id"]: self.ctl.select_mark(mid, from_panel=True))
            e.bind("<FocusIn>", lambda ev, ent=e: self._select_all_later(ent), add="+")
            w[which] = e
            for sym, delta in (("\u2212", -1), ("+", 1)):
                b = small_btn(sym, lambda mid=mark["id"], wh=which, d=delta: self._nudge(mid, wh, d))
                # Tk's built-in auto-repeat: held for 1 s, the command then
                # repeats until release (and release doesn't add an extra step).
                b.configure(repeatdelay=NUDGE_REPEAT_DELAY_MS, repeatinterval=NUDGE_REPEAT_INTERVAL_MS)
                b.grid(row=0, column=col); col += 1
            b = small_btn("@", lambda mid=mark["id"], wh=which: self._to_cursor(mid, wh))
            b.grid(row=0, column=col); col += 1
            w[f"{which}_at"] = b
            # Snap to the neighbor: Start -> previous mark's end, End -> next mark's start.
            if which == "start":
                snap = small_btn("\u21e4", lambda mid=mark["id"]: self._snap(mid, "start"))
                _Tip(snap, "Set Start to the end of the previous mark (0:00 if none)")
            else:
                snap = small_btn("\u21e5", lambda mid=mark["id"]: self._snap(mid, "end"))
                _Tip(snap, "Set End to the start of the next mark (end of audio if none)")
            snap.grid(row=0, column=col); col += 1
            w[f"{which}_snap"] = snap
            # Snap to a stem region boundary: Start -> start of its region,
            # End -> end of its region (repeat to step further out).
            if which == "start":
                rsnap = small_btn("[", lambda mid=mark["id"]: self._snap_region(mid, "start"))
                _Tip(rsnap, "Set Start to the start of its stem region\n(again: the region before)")
            else:
                rsnap = small_btn("]", lambda mid=mark["id"]: self._snap_region(mid, "end"))
                _Tip(rsnap, "Set End to the end of its stem region\n(again: the region after)")
            rsnap.grid(row=0, column=col); col += 1
            w[f"{which}_rsnap"] = rsnap

        filler_col = col
        f.grid_columnconfigure(filler_col, weight=1)
        col += 1
        split = tk.Menubutton(f, text="Split \u25be", bg=BTN_BG, fg=FG, activebackground=BTN_HOVER_BG,
                              activeforeground=FG, relief="flat", bd=1, highlightthickness=0, padx=4, pady=0,
                              cursor="hand2", takefocus=0)
        split_menu = tk.Menu(split, tearoff=False, bg="#ffffff", fg=FG, activebackground=BTN_HOVER_BG,
                             activeforeground=FG)
        split.configure(menu=split_menu)
        split_menu.configure(postcommand=lambda mid=mark["id"], m=split_menu: self._fill_split_menu(mid, m))
        split.grid(row=0, column=col, padx=2); col += 1
        w["split"], w["split_menu"] = split, split_menu
        merge = _style_button(tk.Button(f, text="Merge \u2193", command=lambda mid=mark["id"]: self._merge_next(mid),
                                        padx=4, pady=0))
        merge.grid(row=0, column=col, padx=2); col += 1
        if is_last:
            merge.configure(state="disabled")
        w["merge"] = merge
        delete = _style_button(tk.Button(f, text="\u2715", command=lambda mid=mark["id"]: self._delete(mid),
                                         padx=4, pady=0))
        delete.configure(fg=DELETE_FG, activeforeground=DELETE_FG)
        delete.grid(row=0, column=col, padx=(6, 0)); col += 1
        w["delete"] = delete
        ncols = col

        t = WrapField(f)       # long text wraps; the field grows with it
        t.grid(row=1, column=0, columnspan=ncols, sticky="ew", pady=(3, 0))
        t.bind("<Return>", lambda ev, mid=mark["id"]: (self._commit_text(mid), "break")[1])
        t.bind("<KP_Enter>", lambda ev, mid=mark["id"]: (self._commit_text(mid), "break")[1])
        t.bind("<Shift-Return>", lambda ev: None)     # Shift+Enter: a line break in the text
        t.bind("<FocusOut>", lambda ev, mid=mark["id"]: self._commit_text(mid))
        t.bind("<Escape>", lambda ev, mid=mark["id"]: self._revert(mid))
        t.bind("<FocusIn>", lambda ev, mid=mark["id"]: self.ctl.select_mark(mid, from_panel=True))
        t.bind("<FocusIn>", lambda ev, ent=t: self._select_all_later(ent), add="+")
        w["text"] = t

        # Ctrl+Z / Ctrl+Y in any card field: apply what's typed, then
        # undo/redo the marks (Entry widgets have no undo of their own).
        for entry in (w["start"], w["end"], t):
            for seq in ("<Control-z>", "<Control-Z>"):
                entry.bind(seq, lambda ev, mid=mark["id"]: self._undo_redo(mid, "undo"))
            for seq in ("<Control-y>", "<Control-Y>", "<Control-Shift-z>", "<Control-Shift-Z>"):
                entry.bind(seq, lambda ev, mid=mark["id"]: self._undo_redo(mid, "redo"))

        spacer = tk.Frame(f, height=1, width=400, bg=normal_bg)
        w["labels"].append(spacer)
        spacer.grid(row=2, column=0, columnspan=ncols, sticky="w")
        self.spacers.append(spacer)

        for widget in [f] + list(f.winfo_children()):
            if not isinstance(widget, tk.Entry):
                widget.bind("<Button-1>", lambda ev, mid=mark["id"]: self.ctl.select_mark(mid, from_panel=True),
                            add="+")
        self._forward_wheel(f)
        return w

    def _refresh_gutter(self, delay_ms: int = 40) -> None:
        """Re-align the tab's line-number gutter with the cards. Card lines
        are as tall as the card, so each number is placed beside the card's
        first row (tab.gutter_offsets). Deferred, because the embedded
        windows only have real sizes once Tk has laid them out."""
        tab = self.ctl.tab
        if tab is None or not hasattr(tab, "_update_line_numbers"):
            return

        def run():
            offsets = {}
            if self.mode == "track":
                for i, mid in enumerate(self.order):
                    card = self.cards.get(mid)
                    if not card:
                        continue
                    try:
                        num = card["num"]
                        offsets[2 + i] = int(num.winfo_y()) + int(num.winfo_height()) // 2
                    except (tk.TclError, TypeError, ValueError):
                        pass
            tab.gutter_offsets = offsets or None
            try:
                tab._update_line_numbers()
            except tk.TclError:
                pass
        try:
            self.text.after(delay_ms, run)
        except tk.TclError:
            pass

    def _forward_wheel(self, frame):
        """Embedded widgets swallow the mouse wheel; pass it to the Text
        (and keep the line-number gutter in step)."""
        def wheel(ev):
            if getattr(ev, "num", None) == 4 or getattr(ev, "delta", 0) > 0:
                self.text.yview_scroll(-2, "units")
            else:
                self.text.yview_scroll(2, "units")
            self._refresh_gutter(delay_ms=10)
            return "break"
        for widget in [frame] + list(frame.winfo_children()):
            for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                widget.bind(seq, wheel, add="+")

    def _on_text_configure(self, event=None):
        if self.mode != "track" or not self.spacers:
            return
        try:
            width = max(300, self.text.winfo_width() - 40)
        except tk.TclError:
            return
        for sp in self.spacers:
            try:
                sp.configure(width=width)
            except tk.TclError:
                pass
        self._refresh_gutter()

    # ------------------------------------------------------------------ updating
    def _focused(self):
        try:
            return self.text.focus_get()
        except (KeyError, tk.TclError):  # focus_get can fail on some popups
            return None

    def _set_entry(self, entry, value: str) -> None:
        focused = self._focused()
        if focused is entry or focused is getattr(entry, "widget", None):
            return  # don't clobber what the user is typing
        if entry.get() != value:
            entry.delete(0, "end")
            entry.insert(0, value)

    def _update(self, track, marks, force: bool = False) -> None:
        # Called on every waveform render (10x/s during playback): skip
        # the widget work when nothing visible has changed.
        sig = (track and track.get("name"), self.ctl.selected_mark_id(),
               bool(getattr(self.ctl, "regions", None)),
               getattr(self.ctl, "_play_state", None), getattr(self.ctl, "_play_mark_id", None),
               getattr(self.ctl, "_loop", False),
               tuple((m["id"], m["start"], m.get("end"), m.get("label")) for m in marks))
        if not force and sig == getattr(self, "_last_sig", None):
            return
        self._last_sig = sig
        if self._header_label is not None and track:
            try:
                self._header_label.configure(text=f"Track: {track['name']}   ({len(marks)} marks)")
            except tk.TclError:
                pass
        selected = self.ctl.selected_mark_id()
        for i, m in enumerate(marks):
            card = self.cards.get(m["id"])
            if card is None:
                continue
            try:
                self._set_entry(card["start"], th.format_time_ms(m["start"]))
                is_range = m["type"] == "range" and m.get("end") is not None
                self._set_entry(card["end"], th.format_time_ms(m["end"]) if is_range else "")
                self._set_entry(card["text"], m.get("label") or "")
                card["num"].configure(text=f"#{i + 1}")
                state = self.ctl.mark_play_state(m["id"])
                card["play"].configure(text=PAUSE_GLYPH if state == "playing" else PLAY_GLYPH)
                if state == "paused":
                    card["stop"].grid()
                else:
                    card["stop"].grid_remove()
                has_regions = bool(getattr(self.ctl, "regions", None))
                for key in ("start_rsnap", "end_rsnap"):
                    card[key].configure(state="normal" if has_regions else "disabled")
                bg = self._card_bg(selected=(m["id"] == selected))
                if card["frame"].cget("bg") != bg:
                    self._paint(card, bg)
            except tk.TclError:
                pass

    def _card_bg(self, selected: bool) -> str:
        """Cards use the same colors as the track's marks on the waveform:
        the track color as drawn for its marks, or the selection color for
        the selected mark."""
        if selected:
            return getattr(self.ctl, "SELECTION_COLOR", CARD_SEL_BG)
        track = self.ctl.track_by_id(self.track_id) if self.track_id else None
        if not track:
            return CARD_BG
        try:
            return th.blend_color(track.get("color", "#888888"), 0.85)
        except (ValueError, TypeError):
            return CARD_BG

    def _paint(self, card, bg):
        """Card background (selection / error flash). Buttons and entries
        keep their own colors; label text flips dark/light for contrast."""
        card["frame"].configure(bg=bg)
        fg = contrast_fg(bg)
        for child in card.get("labels", []):
            try:
                child.configure(bg=bg)
                if isinstance(child, tk.Label):
                    child.configure(fg=fg)
            except tk.TclError:
                pass

    def _scroll_to_selected(self):
        mid = self.ctl.selected_mark_id()
        card = self.cards.get(mid)
        if card is None:
            return
        try:
            self.text.see(card["frame"])
        except tk.TclError:
            pass

    def _flash_bad(self, mid):
        card = self.cards.get(mid)
        if not card:
            return
        try:
            self.text.bell()
            self._paint(card, CARD_BAD_BG)
            self.text.after(400, lambda: self._update(self.ctl.track_by_id(self.track_id),
                                                      self.ctl.track_marks(self.track_id), force=True))
        except tk.TclError:
            pass

    def _revert(self, mid):
        card = self.cards.get(mid)
        mark = self.ctl.mark_by_id(mid)
        if not card or not mark:
            return "break"
        is_range = mark["type"] == "range" and mark.get("end") is not None
        for key, value in (("start", th.format_time_ms(mark["start"])),
                           ("end", th.format_time_ms(mark["end"]) if is_range else ""),
                           ("text", mark.get("label") or "")):
            card[key].delete(0, "end")
            card[key].insert(0, value)
        self.text.focus_set()
        return "break"

    # ------------------------------------------------------------------ edits
    def _step(self) -> float:
        try:
            return max(0.001, float(self.step_var.get()))
        except ValueError:
            return 0.1

    def _commit_time(self, mid, which):
        card = self.cards.get(mid)
        mark = self.ctl.mark_by_id(mid)
        if not card or not mark:
            return
        raw = card[which].get().strip()
        if which == "end" and raw == "":
            if mark["type"] == "range":
                self.ctl.set_mark_times(mid, mark["start"], None)
            return
        value = th.parse_time(raw)
        if value is None:
            self._flash_bad(mid)
            return
        duration = self.ctl.audio_duration
        if duration is not None and value > duration:
            value = duration  # typed past the end of the audio: use the end
            if self._focused() is card[which]:
                card[which].delete(0, "end")
                card[which].insert(0, th.format_time_ms(value))
        is_range = mark["type"] == "range" and mark.get("end") is not None
        current = mark["start"] if which == "start" else (mark["end"] if is_range else None)
        if current is not None and abs(value - current) < 0.0005:
            return
        if which == "start":
            ok = self.ctl.set_mark_times(mid, value, mark["end"] if is_range else None)
        else:
            ok = self.ctl.set_mark_times(mid, mark["start"], value)
        if not ok:
            self._flash_bad(mid)

    def _commit_text(self, mid):
        card = self.cards.get(mid)
        mark = self.ctl.mark_by_id(mid)
        if not card or not mark:
            return
        value = card["text"].get().strip()
        if value != (mark.get("label") or ""):
            self.ctl.set_mark_label(mid, value)

    def _commit_all(self, mid):
        """Apply anything typed but not yet committed (buttons don't take
        focus, so a FocusOut may not have happened yet)."""
        self._commit_text(mid)
        self._commit_time(mid, "start")
        self._commit_time(mid, "end")

    def _nudge(self, mid, which, direction):
        """-/+ by the Step, stopping at the boundary's limit (0 / the other
        edge / the end of the audio) -- so holding a button down just runs
        up to the limit and stays there."""
        self._commit_all(mid)
        mark = self.ctl.mark_by_id(mid)
        if not mark:
            return
        step = self._step() * direction
        duration = self.ctl.audio_duration or float("inf")
        is_range = mark["type"] == "range" and mark.get("end") is not None
        if which == "start":
            hi = (mark["end"] - th.MIN_RANGE) if is_range else duration
            new = min(max(0.0, mark["start"] + step), hi)
            if abs(new - mark["start"]) < 1e-9:
                return  # at the limit
            ok = self.ctl.set_mark_times(mid, new, mark["end"] if is_range else None)
        else:
            base = mark["end"] if is_range else mark["start"]
            new = min(max(mark["start"] + th.MIN_RANGE, base + step), duration)
            if is_range and abs(new - mark["end"]) < 1e-9:
                return  # at the limit
            if not is_range and direction < 0:
                return  # a point has no end to shrink
            ok = self.ctl.set_mark_times(mid, mark["start"], new)
        if not ok:
            self._flash_bad(mid)

    def _snap(self, mid, which):
        """Start -> end of the previous mark; End -> start of the next."""
        self._commit_all(mid)
        mark = self.ctl.mark_by_id(mid)
        t = self.ctl.neighbor_time(mid, -1 if which == "start" else 1)
        if not mark or t is None:
            return
        is_range = mark["type"] == "range" and mark.get("end") is not None
        if which == "start":
            ok = self.ctl.set_mark_times(mid, t, mark["end"] if is_range else None)
        else:
            ok = self.ctl.set_mark_times(mid, mark["start"], t)
        if not ok:
            self._flash_bad(mid)

    def _snap_region(self, mid, which):
        """Start -> start of its stem region; End -> end of its region."""
        self._commit_all(mid)
        mark = self.ctl.mark_by_id(mid)
        if not mark:
            return
        is_range = mark["type"] == "range" and mark.get("end") is not None
        if which == "start":
            t = self.ctl.region_boundary(mark["start"], -1)
            ok = t is not None and self.ctl.set_mark_times(mid, t, mark["end"] if is_range else None)
        else:
            base = mark["end"] if is_range else mark["start"]
            t = self.ctl.region_boundary(base, 1)
            ok = t is not None and self.ctl.set_mark_times(mid, mark["start"], t)
        if not ok:
            self._flash_bad(mid)

    def _toggle_play(self, mid):
        loop = getattr(self, "_shift_on_play", False)
        self._shift_on_play = False
        self._commit_all(mid)
        self.ctl.toggle_mark_play(mid, loop=loop)

    def _select_all_later(self, entry):
        """Clicking into a field selects its whole value (after Tk's own
        click handling, which would otherwise just place the cursor)."""
        def select():
            try:
                entry.select_range(0, "end")
                entry.icursor("end")
            except tk.TclError:
                pass
        try:
            entry.after(1, select)
        except tk.TclError:
            pass

    def _click_off(self, event=None):
        """A click in the panel outside any card: commit what's being typed,
        drop keyboard focus from the card and deselect it (the panel stays
        on the track). Ignored while the mouse is busy with a canvas drag."""
        if self.mode != "track" or self.ctl.mouse_busy():
            return None
        try:
            self.text.focus_set()   # FocusOut on the card field commits it
        except tk.TclError:
            pass
        if self.track_id:
            self.ctl.select_track_only(self.track_id)
        return "break" if event is not None and event.widget is self.text else None

    def _delete(self, mid):
        """Delete this card's mark; the next card (or the previous one, if
        this was the last) becomes the selected card."""
        self.text.focus_set()  # this card is about to go away
        self.ctl.delete_mark_by_id(mid)
        self._scroll_to_selected()

    def _to_cursor(self, mid, which):
        self._commit_all(mid)
        mark = self.ctl.mark_by_id(mid)
        pos = self.ctl.cursor_position()
        if not mark or pos is None:
            return
        is_range = mark["type"] == "range" and mark.get("end") is not None
        if which == "start":
            ok = self.ctl.set_mark_times(mid, pos, mark["end"] if is_range else None)
        else:
            ok = self.ctl.set_mark_times(mid, mark["start"], pos)
        if not ok:
            self._flash_bad(mid)

    def _undo_redo(self, mid, which):
        self._commit_all(mid)
        self.text.focus_set()  # the card may be rebuilt; don't leave focus in it
        (self.ctl.undo_marks if which == "undo" else self.ctl.redo_marks)()
        return "break"

    def _fill_split_menu(self, mid, menu):
        """Built as the Split \u25be menu opens -- the text selection and
        cursor are read now, before the click moves the focus."""
        card = self.cards.get(mid)
        mark = self.ctl.mark_by_id(mid)
        if not card or not mark:
            return
        sel = card["text"].selected_span()
        insert = card["text"].index("insert")
        self._split_ctx = {"mid": mid, "sel": sel, "insert": insert}
        label = card["text"].get()
        n_words = len(label.split())
        try:
            menu.delete(0, "end")
        except tk.TclError:
            pass
        menu.add_command(label="Split at cursor", command=lambda: self._split(mid))
        menu.add_command(label="Split selected phrase", state="normal" if sel else "disabled",
                         command=lambda: self._split_phrase(mid))
        menu.add_command(label=f"Split into words ({n_words})", state="normal" if n_words >= 2 else "disabled",
                         command=lambda: self._split_words(mid))

    def _split_phrase(self, mid):
        """Before / selected / after (empty parts dropped), timed by word weights."""
        ctx = getattr(self, "_split_ctx", None) or {}
        card = self.cards.get(mid)
        sel = ctx.get("sel") if ctx.get("mid") == mid else None
        if sel is None and card:
            sel = card["text"].selected_span()
        self._commit_all(mid)
        mark = self.ctl.mark_by_id(mid)
        if not mark or not sel:
            self._flash_bad(mid)
            return
        n = len(mark.get("label") or "")
        spans = [(0, sel[0]), (sel[0], sel[1]), (sel[1], n)]
        if not self.ctl.split_mark_into(mid, spans):
            self._flash_bad(mid)

    def _split_words(self, mid):
        """One card per word, timed by syllables (with small gaps at
        punctuation and line breaks)."""
        self._commit_all(mid)
        mark = self.ctl.mark_by_id(mid)
        if not mark or not self.ctl.split_mark_into(mid, th.word_spans(mark.get("label") or "")):
            self._flash_bad(mid)

    def _split(self, mid):
        card = self.cards.get(mid)
        if not card:
            return
        ctx = getattr(self, "_split_ctx", None) or {}
        try:
            text_index = ctx["insert"] if ctx.get("mid") == mid else card["text"].index("insert")
        except tk.TclError:
            text_index = None
        self._split_ctx = None
        self._commit_all(mid)
        if not self.ctl.split_mark_by_id(mid, text_index=text_index):
            self._flash_bad(mid)

    def _merge_next(self, mid):
        self._commit_all(mid)
        if not self.ctl.merge_mark_by_id(mid, direction=1):
            self._flash_bad(mid)
