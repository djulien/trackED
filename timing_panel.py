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
  - \u2196 \u2197 / \u2199 \u2198: Start to the foot of the previous / next rising
    edge in the audio, End to the bottom of the previous / next falling
    edge (again: the one after that). In the vocals stem when it's been
    separated; Shift+click: the full mix. See timing_helpers.edge_times.
  - Typing in a card marks the tab unsaved at once; saving (File > Save
    or auto-save) applies what's typed first (except a time still being
    typed in).
  - While playing, the card the playhead is in is shown in green.
  - "rest" (after End): a 3-state button -- off / all / to gap. While on,
    End changes on any card (-/+, typed, @, ], \u2198) also move the later
    marks in the track by the same amount: all of them, or just the ones
    up to the first gap (not the \u21e5 snap, which aims at the next mark).
  - Merge v: merges this mark with the next one in the track into one
    range (labels joined, voices combined).
  - Voice v: the card's voices (any number of the file's user-defined
    voices), plus New voice... ("voice N" by default). The header's Show
    box limits the cards to one voice (or those without any).
  - Syllables / time per word: hover over a word in the text for its
    syllable count and the time it would get as its own card. Right-click
    a word, or Alt+Up/Down (syllables) and Alt+Right/Left (time, by the
    header's Step) with the text cursor in it, to adjust: that writes
    "word {+1}" / "word {-0.1s}" into the text (see
    timing_helpers.word_infos).

When nothing track-related is selected the panel shows the tab's normal
information text again. Not a *_tab.py file, so plugin discovery skips it.
"""

from __future__ import annotations

import re
import time
import tkinter as tk
from tkinter import ttk
from typing import Dict, List, Optional

from utils import insert_styled_text, register_modifier_button, crumb, fast_destroy

import timing_helpers as th

STEP_CHOICES = ["0.01", "0.05", "0.1", "0.25", "0.5", "1.0"]

# Every classic-Tk widget here gets explicit colors (the desktop theme's
# defaults can't be relied on). The cards are dark, like the text panel
# around them, so scrolling doesn't flash light/dark.
DARK_TEXT = "#1e1e1e"
LIGHT_TEXT = "#e6e6e6"
FG = LIGHT_TEXT
FG_DIM = "#9a9a9a"
FG_DISABLED = "#6a6a6a"
HEADER_BG = "#2a2a2a"
CARD_BG = "#333333"
CARD_DARK_BASE = "#2b2b2b"   # track / selection colors are blended toward this for card backgrounds
CARD_SEL_BG = "#5a5220"
CARD_BAD_BG = "#6a2a2a"
CARD_PLAY_BG = "#2f5f2f"     # the card the playhead is in, while playing
ENTRY_BG = "#1b1b1b"
BTN_BG = "#454545"
BTN_HOVER_BG = "#58677a"
BTN_PRESS_BG = "#3b5a86"
DELETE_FG = "#ff7a7a"
FG_ON_DARK = LIGHT_TEXT
MENU_BG, MENU_FG, MENU_ACTIVE_BG = "#ffffff", DARK_TEXT, "#cfe0ff"     # pop-up menus stay light
TIP_BG, TIP_FG = "#ffffe0", DARK_TEXT
MOD_HINT_FG = "#ffb000"      # buttons whose Shift+click differs, while Shift is held
NUDGE_REPEAT_DELAY_MS = 1000   # hold -/+ this long, then it auto-repeats
NUDGE_REPEAT_INTERVAL_MS = 80


SHIFT_MASK = 0x0001
CONTROL_MASK = 0x0004
PLAY_GLYPH, PAUSE_GLYPH = "\u25b6", "\u275a\u275a"
SHOW_ALL = "All cards"      # Show: filter -- every card
MULTI_CARD_LINES = 3      # card text fields grow to at most this many lines when a track has several cards
LIST_BG = "#1e1e1e"       # the card list's background (between cards)
CARD_GAP = 3              # pixels between cards
WHEEL_UNITS = 3           # mouse-wheel step in the card list
PLAY_LOOKAHEAD_CARDS = 2  # while playing, keep this many cards after the current one in view
BUILD_AT_ONCE = 40        # tracks with more cards than this are built in slices ("Loading track ...")
BUILD_SLICE_SEC = 0.05    # work per event-loop pass while building
BUILD_MIN_CARDS = 5       # ...but at least this many cards per pass
REST_MODES = ("off", "group", "all")
REST_TEXT = {"off": "Join> none", "group": "Join> group", "all": "Join> all"}
REST_BTN_WIDTH = 11
JOIN_MODES = ("off", "group", "all")
JOIN_TEXT = {"off": "<Join none", "group": "<Join group", "all": "<Join all"}
JOIN_BTN_WIDTH = 11
ALL_VOICES = "All voices"    # a card with no voice set is for all voices (Show: filter too)
WORD_TIP_DELAY_MS = 600
VOICE_BTN_MAX_CHARS = 18


def voice_button_text(voices, label: str = "") -> str:
    """Text for a card's Voice button: its voices -- or, with none set,
    the voice its lyrics imply ("voice 2" for text all in parentheses,
    "voice 1" for text that mixes both) -- with a "+" when the text mixes
    parenthesized and plain lyrics."""
    voices = list(voices or [])
    label = label or ""
    whole = th.in_parentheses(label, (0, len(label))) if label.strip() else False
    mixed = not whole and th.has_parentheses(label)
    if not voices:
        if whole:
            voices = [th.paren_voice_name([])]
        elif mixed:
            voices = [th.VOICE_PREFIX + "1"]
    if not voices:
        return ALL_VOICES + " \u25be"
    text = ", ".join(voices)
    if len(text) > VOICE_BTN_MAX_CHARS:
        text = text[:VOICE_BTN_MAX_CHARS - 1] + "\u2026"
    return text + ("+" if mixed else "") + " \u25be"


def describe_word(info) -> str:
    """Tooltip text for one word_timings() entry."""
    word = info["word"]
    syl = info["syllables"]
    line = f"\u201c{word}\u201d  {syl} syllable{'s' if syl != 1 else ''}"
    if info["syl_adj"]:
        line += f" (estimate {info['base']}, {info['syl_adj']:+d})"
    if info.get("seconds") is not None:
        line += f"  \u00b7  \u2248{info['seconds']:.2f} s as a word card"
    if info["time_adj"]:
        line += f" (incl. {th.format_adjust_seconds(info['time_adj'])})"
    return line + "\nRight-click to adjust  \u00b7  Alt+\u2191/\u2193 syllables  \u00b7  Alt+\u2192/\u2190 time"


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
            tk.Label(self._tip, text=self.text, background=TIP_BG, foreground=TIP_FG, relief="solid",
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
    return DARK_TEXT if (0.299 * r + 0.587 * g + 0.114 * b) > 0.55 else LIGHT_TEXT


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


_FIELD_FONT = None


def _field_font():
    """The card text fields' font, as one tkinter.font.Font (made once)."""
    global _FIELD_FONT
    if _FIELD_FONT is None:
        import tkinter.font as tkfont
        _FIELD_FONT = tkfont.Font(family="TkDefaultFont", size=10)
    return _FIELD_FONT


class WrapField:
    """The card's text field: a word-wrapping tk.Text that grows to fit
    its text (up to MAX_LINES), with the small Entry-like API the panel
    uses (get / delete(0, "end") / insert(0, s) / index("insert") /
    icursor / select_range / selected_span). Enter commits (Shift+Enter
    inserts a line break); anything else is passed through to the Text."""

    MAX_LINES = 20           # absolute cap (a track's only card may use the panel's height)
    max_lines = 0            # set by the panel: 3 in a track with several cards (0: MAX_LINES)

    def __init__(self, parent):
        # The text is only put into the Text widget once Tk has given it a
        # real width (_pending until then). A Text laid out at its initial
        # 1-pixel width wraps a long label into one line per character --
        # with word wrap that work grows with the square of the length,
        # which is what froze the app on showing a track whose card holds
        # a long label.
        self._pending = ""
        self.widget = tk.Text(parent, height=1, width=20, wrap="word", undo=False, font=("TkDefaultFont", 10),
                              bg=ENTRY_BG, fg=FG, insertbackground=FG, selectbackground="#264f78",
                              selectforeground="#ffffff", relief="solid", bd=1, highlightthickness=1,
                              highlightcolor="#7aa7e0", highlightbackground="#555555", padx=3, pady=2)
        self.widget.bind("<Configure>", lambda e: self._on_configure(), add="+")
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

    def _laid_out(self) -> bool:
        try:
            return int(self.widget.winfo_width()) > 1
        except (tk.TclError, TypeError, ValueError):
            return True

    def _on_configure(self):
        if self._pending is not None and self._laid_out():
            text, self._pending = self._pending, None
            if text:
                self.widget.insert("1.0", text)
        self.fit()

    def get(self) -> str:
        if self._pending is not None:
            return self._pending
        return self.widget.get("1.0", "end-1c")

    def delete(self, first=0, last="end") -> None:
        if self._pending is not None:
            self._pending = ""
            return
        self.widget.delete("1.0", "end")

    def insert(self, index, text) -> None:
        if self._pending is not None and not self._laid_out():
            pos = len(self._pending) if index == "end" else max(0, min(len(self._pending), int(index)))
            self._pending = self._pending[:pos] + text + self._pending[pos:]
            self.fit()
            return
        if self._pending is not None:              # laid out by now: move the text in first
            pending, self._pending = self._pending, None
            if pending:
                self.widget.insert("1.0", pending)
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

    FLIP_WINDOW_SEC = 0.5
    estimate_px = 0          # width to assume before Tk has laid the field out (set by the panel)

    def estimate_lines(self, width_px: int) -> int:
        """Display lines the text would take at this width (word wrap,
        measured with the field's font) -- without asking Tk to lay it out."""
        try:
            import tkinter.font as tkfont
            font = _field_font()
            space = font.measure(" ")
            avail = max(40, int(width_px) - 12)          # padding, border
            lines = 0
            for para in (self.get() or "").split("\n"):
                lines += 1
                x = 0
                for word in para.split(" "):
                    w = font.measure(word)
                    if x and x + space + w > avail:
                        lines += 1
                        x = w
                    else:
                        x = x + space + w if x else w
            return max(1, lines)
        except (tk.TclError, TypeError, ValueError, AttributeError, ImportError):
            return 1

    def fit(self) -> None:
        """Height = number of wrapped display lines (1..MAX_LINES).

        Damped: a new height that just undoes the previous change (within
        FLIP_WINDOW_SEC) is skipped, keeping the taller one. Otherwise a
        long label right at a wrapping width can make the layout see-saw:
        taller -> the card shifts the panel's layout -> narrower/wider ->
        shorter -> ... without end."""
        laid_out = self._laid_out()
        if laid_out and self._pending is not None:
            text, self._pending = self._pending, None
            if text:
                self.widget.insert("1.0", text)
        try:
            if laid_out:
                lines = _count(self.widget.count("1.0", "end", "displaylines")) or 1
            elif self.estimate_px:
                # Not laid out yet: counting display lines now would use a
                # 1-pixel width (every card went to 8 lines, then back to 1
                # once shown -- 75 cards' worth of re-layout).
                lines = self.estimate_lines(self.estimate_px)
            else:
                return

            lines = max(1, min(self.max_lines or self.MAX_LINES, lines))
            current = int(self.widget.cget("height") or 1)
            if current == lines:
                return
            now = time.monotonic()
            last = getattr(self, "_last_fit", None)        # (time, from, to)
            if last and now - last[0] < self.FLIP_WINDOW_SEC and last[1] == lines and last[2] == current \
                    and lines < current:
                return                     # it would just undo the last change
            self._last_fit = (now, current, lines)
            crumb(f"card text height {current}->{lines}")
            self.widget.configure(height=lines)
        except (tk.TclError, TypeError, ValueError):
            pass


def _style_entry(entry: tk.Entry) -> tk.Entry:
    entry.configure(bg=ENTRY_BG, fg=FG, insertbackground=FG, disabledforeground=FG_DISABLED,
                    selectbackground="#264f78", selectforeground="#ffffff",
                    relief="solid", bd=1, highlightthickness=1, highlightcolor="#7aa7e0",
                    highlightbackground="#555555")
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
        self.voice_filter_var = tk.StringVar(value=SHOW_ALL)
        # "rest": End changes on a card also move the later marks -- "off",
        # "all" (every later mark) or "gap" (up to the first gap). One
        # setting shared by all cards; not saved.
        self.rest_mode = "off"
        self.join_mode = "off"        # <Join: Start changes also end the previous card there (not saved)
        self.playing_mid = None       # card under the playhead (see set_playing_mark)
        self._shift_edge = False
        self._word_tip = None
        self._word_tip_after = None
        self._header_label = None
        self._extras: List[tk.Widget] = []
        try:
            self.text.bind("<Button-1>", self._click_off, add="+")
            # Up/Down in the card list: the previous/next card (instead of
            # the Text widget moving its cursor across the embedded cards)
            self.text.bind("<Up>", lambda e: self.select_adjacent_card(-1), add="+")
            self.text.bind("<Down>", lambda e: self.select_adjacent_card(1), add="+")
        except tk.TclError:
            pass

    # ------------------------------------------------------------------ public
    def teardown(self) -> None:
        """App closing: delete every card line at once (Tk destroys the
        embedded cards with them) and stop reacting to anything."""
        self.mode = "closing"
        self._build_gen = getattr(self, "_build_gen", 0) + 1     # stop a build in progress
        if getattr(self, "list", None) is not None:
            fast_destroy(self.list)              # the canvas and every card in one Tk call
            self.list = None
        self.cards, self.order = {}, []

    def sync(self, force: bool = False) -> None:
        if self.mode == "closing":
            return
        """Called after every waveform render: decide which view to show,
        and update it with as little churn as possible (entries being
        edited keep their contents and focus)."""
        track_id = self.ctl.panel_track_id()
        if track_id is None:
            if self.mode != "info" or force:
                self.show_info()
            return
        track = self.ctl.track_by_id(track_id)
        marks = self.visible_marks(track_id)
        ids = [m["id"] for m in marks]
        if force or self.mode != "track" or track_id != self.track_id:
            crumb(f"panel.sync: build {len(marks)} cards")
            self._build(track, marks)
        elif ids != self.order:
            # same track, some cards added/removed/moved (delete, split,
            # merge, a time edit past a neighbor): change just those cards
            crumb(f"panel.sync: patch to {len(marks)} cards")
            if getattr(self, "building", False) or not self._patch(marks):
                self._build(track, marks)
            else:
                self._update(track, marks)
        else:
            self._update(track, marks)

    def visible_marks(self, track_id):
        """The track's marks, limited to the header's voice choice."""
        marks = self.ctl.track_marks(track_id)
        want = self.voice_filter_var.get()
        if want == ALL_VOICES:
            return [m for m in marks if not m.get("voices")]
        if want and want != SHOW_ALL and want in getattr(self.ctl, "voices", []):
            return [m for m in marks if want in (m.get("voices") or [])]
        return marks

    def _on_voice_filter(self, event=None):
        self.sync(force=True)

    def show_info(self) -> None:
        self._clear()
        self._show_list(False)
        self.mode = "info"
        self.track_id = None
        self._with_text(lambda: (self.text.delete("1.0", "end"), insert_styled_text(self.text, self.ctl.info_text)))

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

    # ------------------------------------------------------------------ the card list
    # The cards live in their own canvas (with its own scrollbar), laid
    # over the tab's text panel while a track is shown -- not embedded in
    # the Text widget: Tk's text layout with a few dozen embedded cards was
    # slow to clear, laggy to scroll, and could lock up for good (the
    # stall reports). On a canvas each card is a window item we place
    # ourselves (_relayout), one below the other.

    def _ensure_list(self):
        if getattr(self, "list", None) is not None:
            return
        host = self.text.master
        self.list = tk.Frame(host, bg=LIST_BG)
        self.header_holder = tk.Frame(self.list, bg=HEADER_BG)
        self.header_holder.pack(side="top", fill="x")
        body = tk.Frame(self.list, bg=LIST_BG)
        body.pack(side="top", fill="both", expand=True)
        self.canvas = tk.Canvas(body, bg=LIST_BG, highlightthickness=0, bd=0, takefocus=1)
        self.vsb = ttk.Scrollbar(body, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.vsb.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.canvas.bind("<Configure>", self._on_list_configure, add="+")
        self.canvas.bind("<Button-1>", self._click_off, add="+")
        self.canvas.bind("<Up>", lambda e: self.select_adjacent_card(-1))
        self.canvas.bind("<Down>", lambda e: self.select_adjacent_card(1))
        self._bind_wheel(self.canvas)
        self._bind_wheel(self.header_holder)

    def _focus_list(self):
        target = self.canvas if getattr(self, "list", None) is not None and self.mode == "track" else self.text
        try:
            target.focus_set()
        except tk.TclError:
            pass

    def _show_list(self, on):
        lst = getattr(self, "list", None)
        if lst is None:
            return
        try:
            if on:
                lst.place(x=0, y=0, relwidth=1, relheight=1)
                lst.lift()
            else:
                lst.place_forget()
        except tk.TclError:
            pass

    def _list_width(self) -> int:
        try:
            width = int(self.canvas.winfo_width())
        except (tk.TclError, TypeError, ValueError, AttributeError):
            width = 0
        return width if width > 50 else 900

    def _list_height(self) -> int:
        try:
            height = int(self.canvas.winfo_height())
        except (tk.TclError, TypeError, ValueError, AttributeError):
            height = 0
        return height if height > 1 else 200

    def _on_list_configure(self, event=None):
        """The list was resized: cards take its width; the text-field cap
        follows its height."""
        if self.mode != "track":
            return
        width = self._list_width()
        crumb(f"panel list size {width}x{self._list_height()}")
        if width == getattr(self, "_items_width", None):
            self._apply_field_cap()
            self._schedule_relayout()
            return
        self._items_width = width
        for card in self.cards.values():
            try:
                self.canvas.itemconfigure(card["item"], width=width)
            except (tk.TclError, KeyError):
                pass
        self._apply_field_cap()
        self._schedule_relayout()

    def _schedule_relayout(self, delay_ms=1):
        if getattr(self, "_relayout_pending", None) is None:
            try:
                self._relayout_pending = self.canvas.after(delay_ms, self._relayout)
            except (tk.TclError, AttributeError):
                self._relayout_pending = None

    def _card_height(self, card) -> int:
        try:
            return max(1, int(card["frame"].winfo_reqheight()))
        except (tk.TclError, TypeError, ValueError):
            return 60

    def _relayout(self):
        """Stack the cards in order, each below the one before."""
        self._relayout_pending = None
        if self.mode != "track" or getattr(self, "list", None) is None:
            return
        t0 = time.monotonic()
        y = CARD_GAP
        positions = {}
        waiting = 0
        for mid in self.order:
            card = self.cards.get(mid)
            if card is None:
                continue
            height = self._card_height(card)
            if not card.get("shown"):
                if height <= 2:            # size not known yet: keep it hidden, come back
                    waiting += 1
                    continue
                try:
                    self.canvas.itemconfigure(card["item"], state="normal")
                except (tk.TclError, KeyError):
                    pass
                card["shown"] = True
            positions[mid] = y
            if card.get("y") != y:              # only move what moved (each move is X-server work)
                try:
                    self.canvas.coords(card["item"], 0, y)
                    card["y"] = y
                except (tk.TclError, KeyError):
                    pass
            y += height + CARD_GAP
        if waiting:
            self._schedule_relayout(delay_ms=30)
        elif getattr(self, "_see_when_ready", False):
            self._see_when_ready = False          # all cards placed: now the selected one can be shown
            self.canvas.after(1, self._scroll_to_selected)
        self._positions = positions
        try:
            self.canvas.delete("listnote")
            note = None
            if self.building or waiting:
                note = f"Loading track ... {len(self.cards) - waiting} of {len(self.order)} cards"
            elif not self.order:
                note = "(no marks in this track yet -- drag marks from the waveform into its band)"
            if note:
                self.canvas.create_text(10, y + 8, text=note, anchor="nw", fill=FG_DIM, tags=("listnote",))
                y += 30
            self.canvas.configure(scrollregion=(0, 0, self._list_width(), y + CARD_GAP))
        except (tk.TclError, TypeError):
            pass
        crumb(f"panel._relayout {len(positions)} shown, {waiting} waiting, "
              f"{1000 * (time.monotonic() - t0):.0f} ms")

    def _see(self, mid):
        """Scroll the list so this card is in view."""
        card = self.cards.get(mid)
        if card is None or getattr(self, "list", None) is None:
            return
        if getattr(self, "_relayout_pending", None) is not None:
            try:
                self.canvas.after_cancel(self._relayout_pending)
            except (tk.TclError, ValueError):
                pass
            self._relayout()
        y0 = (getattr(self, "_positions", {}) or {}).get(mid)
        if y0 is None:
            return
        y1 = y0 + self._card_height(card)
        try:
            region = self.canvas.cget("scrollregion")
            parts = list(region) if isinstance(region, (tuple, list)) else str(region).split()
            total = float(parts[3]) if len(parts) >= 4 else 0.0
            top = float(self.canvas.canvasy(0))
            view = float(self._list_height())
        except (tk.TclError, TypeError, ValueError, IndexError):
            return
        if total <= view or total <= 0:
            return
        if y0 < top:
            self.canvas.yview_moveto(max(0.0, (y0 - CARD_GAP) / total))
        elif y1 > top + view:
            self.canvas.yview_moveto(min(1.0, (y1 + CARD_GAP - view) / total))

    def _bind_wheel(self, widget):
        def wheel(ev):
            if getattr(ev, "num", None) == 4 or getattr(ev, "delta", 0) > 0:
                self.canvas.yview_scroll(-WHEEL_UNITS, "units")
            else:
                self.canvas.yview_scroll(WHEEL_UNITS, "units")
            return "break"
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            try:
                widget.bind(seq, wheel, add="+")
            except tk.TclError:
                pass

    def _clear(self) -> None:
        """Remove the shown cards: their canvas items go at once, the
        (now hidden) card widgets are destroyed a few at a time afterwards
        (_dispose), so the next track appears right away."""
        crumb(f"panel._clear ({len(self.cards)} cards)")
        old = [card["frame"] for card in self.cards.values()] + list(getattr(self, "_extras", []))
        for extra in getattr(self, "_extras", []):      # the old header: out of sight now
            try:
                extra.pack_forget()
            except tk.TclError:
                pass
        self._extras = []
        self.cards = {}
        self.order = []
        self._positions = {}
        if getattr(self, "list", None) is not None:
            try:
                self.canvas.delete("all")
            except tk.TclError:
                pass
        if old:
            self._trash = getattr(self, "_trash", []) + old
            self._schedule_dispose()
        crumb("panel._clear done")

    DISPOSE_PER_PASS = 25

    def _schedule_dispose(self):
        if getattr(self, "_dispose_pending", None) is None:
            try:
                self._dispose_pending = self.text.after(50, self._dispose)
            except tk.TclError:
                self._dispose_pending = None

    def _dispose(self):
        """Destroy a few old cards' Python wrappers (their Tk windows are
        already gone with the text), then come back for more."""
        self._dispose_pending = None
        trash = getattr(self, "_trash", [])
        for widget in trash[:self.DISPOSE_PER_PASS]:
            fast_destroy(widget)
        del trash[:self.DISPOSE_PER_PASS]
        if trash:
            self._schedule_dispose()

    def _build(self, track, marks) -> None:
        """Show a track's cards. A short track is built at once; a long one
        shows "Loading track ..." and is built in slices (BUILD_SLICE_SEC
        of work per event-loop pass), so the window stays responsive and
        the first cards appear right away."""
        self._clear()
        self._ensure_list()
        self.mode = "track"
        self._show_list(True)
        self.track_id = track["id"] if track else None
        self.order = [m["id"] for m in marks]
        self._build_gen = getattr(self, "_build_gen", 0) + 1
        self.building = False
        self._make_header(track, marks).pack(side="left", fill="x", expand=True)
        crumb(f"panel._build {len(marks)} cards")
        if len(marks) <= BUILD_AT_ONCE:
            self._add_cards(marks, 0, len(marks))
            self._finish_build(track, marks)
            return
        self.building = True
        self._relayout()
        try:
            self.canvas.after(1, lambda gen=self._build_gen: self._build_slice(gen, track, marks, 0))
        except tk.TclError:
            self._build_slice(self._build_gen, track, marks, 0)

    def _add_cards(self, marks, start, stop):
        for i in range(start, stop):
            self._insert_card(i, marks[i], i == len(marks) - 1)

    def _insert_card(self, index, mark, is_last):
        card = self._make_card(index, mark, is_last=is_last)
        # Hidden until Tk has worked out its size (_relayout shows it):
        # before that every card is 1 pixel tall, and a fresh track showed
        # as a stack of thin lines for seconds.
        card["item"] = self.canvas.create_window(0, 0, anchor="nw", window=card["frame"], width=self._list_width(),
                                                 state="hidden", tags=("card",))
        card["shown"] = False
        card["frame"].bind("<Configure>", lambda e: self._schedule_relayout(), add="+")
        self.cards[mark["id"]] = card
        return card

    def _remove_card(self, mid):
        card = self.cards.pop(mid, None)
        if card is None:
            return
        try:
            self.canvas.delete(card["item"])
        except (tk.TclError, KeyError):
            pass
        self._trash = getattr(self, "_trash", []) + [card["frame"]]
        self._schedule_dispose()

    def _patch(self, marks) -> bool:
        """Bring the shown cards in line with `marks`: remove the cards
        that went, make the new ones, and restack (cards that only moved
        are just placed elsewhere)."""
        new = [m["id"] for m in marks]
        if not self.order or not new:
            return False
        wanted = set(new)
        remove = [mid for mid in self.order if mid not in wanted]
        add = [i for i, mid in enumerate(new) if mid not in self.cards]
        crumb(f"panel._patch -{len(remove)} +{len(add)}")
        for mid in remove:
            self._remove_card(mid)
        for i in add:
            self._insert_card(i, marks[i], i == len(marks) - 1)
        self.order = new
        self._last_sig = None
        self._apply_field_cap()                 # a track can go from one card to several, or back
        self._relayout()
        return True

    def _build_slice(self, gen, track, marks, start):
        if gen != self._build_gen or self.mode != "track":
            return                        # another track (or the info view) replaced this build
        crumb(f"panel build slice from {start}")
        t0 = time.monotonic()
        stop = start
        while stop < len(marks) and (stop - start < BUILD_MIN_CARDS or time.monotonic() - t0 < BUILD_SLICE_SEC):
            self._add_cards(marks, stop, stop + 1)
            stop += 1
        if stop < len(marks):
            self._relayout()
            try:
                self.canvas.after(1, lambda: self._build_slice(gen, track, marks, stop))
            except tk.TclError:
                pass
            return
        self.building = False
        # the track may have changed while building: rebuild if so, else finish
        current = self.visible_marks(self.track_id) if self.track_id else []
        if [m["id"] for m in current] != self.order:
            self.sync(force=True)
            return
        self._finish_build(self.ctl.track_by_id(self.track_id), current)

    def _finish_build(self, track, marks):
        crumb("panel._finish_build")
        self._field_cap = None                 # the cap depends on the number of cards too
        self._apply_field_cap()
        self._update(track, marks, force=True)
        self._see_when_ready = True
        self._relayout()
        crumb("panel._finish_build done")

    def _make_header(self, track, marks):
        frame = tk.Frame(self.header_holder, bg=HEADER_BG, padx=6, pady=3)
        self._extras.append(frame)
        name = track["name"] if track else "?"
        swatch = tk.Frame(frame, width=12, height=12, bg=(track or {}).get("color", "#888888"))
        swatch.pack(side="left", padx=(0, 6))
        self._header_label = tk.Label(frame, text=self._header_text(track, marks),
                                      font=("TkDefaultFont", 10, "bold"), bg=HEADER_BG, fg=FG)
        self._header_label.pack(side="left")
        nudge = tk.Label(frame, text="   Nudge size:", bg=HEADER_BG, fg=FG)
        nudge.pack(side="left")
        combo = ttk.Combobox(frame, textvariable=self.step_var, values=STEP_CHOICES, width=5)
        combo.pack(side="left", padx=(2, 10))
        for widget in (nudge, combo):
            _Tip(widget, "Seconds the \u2212 / + buttons (and Alt+arrows on a word) move a time")
        tk.Label(frame, text="Show:", bg=HEADER_BG, fg=FG).pack(side="left")
        voices = list(getattr(self.ctl, "voices", []))
        if self.voice_filter_var.get() not in [SHOW_ALL, ALL_VOICES] + voices:
            self.voice_filter_var.set(SHOW_ALL)
        vbox = ttk.Combobox(frame, textvariable=self.voice_filter_var, state="readonly", width=14,
                            values=[SHOW_ALL] + voices + [ALL_VOICES])
        vbox.pack(side="left", padx=(2, 10))
        vbox.bind("<<ComboboxSelected>>", self._on_voice_filter)
        self._voice_filter_box = vbox
        hint = tk.Label(frame, text="Click the waveform to place the @cursor (Split \u25be can split there)",
                        fg=FG_DIM, bg=HEADER_BG)
        hint.pack(side="left")
        # Clicking the header's background also "clicks off" the cards.
        for widget in (frame, swatch, self._header_label, hint):
            widget.bind("<Button-1>", self._click_off, add="+")
        self._forward_wheel(frame)
        return frame

    def _header_text(self, track, marks):
        name = track["name"] if track else "?"
        total = len(self.ctl.track_marks(track["id"])) if track else len(marks)
        if total != len(marks):
            return f"Track: {name}   ({len(marks)} of {total} marks)"
        return f"Track: {name}   ({len(marks)} marks)"

    def _make_card(self, index, mark, is_last):
        normal_bg = self._card_bg(selected=False)
        f = tk.Frame(self.canvas, bg=normal_bg, bd=1, relief="groove", padx=4, pady=3)
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
                  lambda ev: (setattr(self, "_shift_on_play", bool(ev.state & SHIFT_MASK)),
                              setattr(self, "_ctrl_on_play", bool(ev.state & CONTROL_MASK))), add="+")
        for seq in ("<Enter>", "<Motion>"):
            play.bind(seq, lambda ev, b=play: b.configure(cursor="exchange" if ev.state & SHIFT_MASK
                                                           else "hand2"), add="+")
        _Tip(play, "Play / pause this mark\nWhile paused: Play starts it again from its start;\n"
                   "Ctrl+click resumes from the paused spot\nShift+click: loop it until paused")
        register_modifier_button(play, ("shift", "control"))

        w["tbtns"] = []          # the Start/End buttons: they take the card's background

        def time_btn(text, cmd, tip=None, repeat=False):
            nonlocal col
            btn = tk.Button(f, text=text, command=cmd, padx=2, pady=0, width=2, bg=normal_bg,
                            fg=contrast_fg(normal_bg), activebackground=normal_bg,
                            activeforeground=contrast_fg(normal_bg), disabledforeground=FG_DISABLED,
                            relief="flat", overrelief="raised", bd=1, highlightthickness=0,
                            cursor="hand2", takefocus=0)
            btn._rest_bg, btn._mod_normal_fg = normal_bg, contrast_fg(normal_bg)
            btn.bind("<Enter>", lambda _e, b_=btn: str(b_.cget("state")) != "disabled"
                     and b_.configure(bg=BTN_HOVER_BG), add="+")
            btn.bind("<Leave>", lambda _e, b_=btn: b_.configure(bg=b_._rest_bg), add="+")
            if repeat:
                # Tk's built-in auto-repeat: held for 1 s, the command then
                # repeats until release (and release doesn't add an extra step).
                btn.configure(repeatdelay=NUDGE_REPEAT_DELAY_MS, repeatinterval=NUDGE_REPEAT_INTERVAL_MS)
            if tip:
                _Tip(btn, tip)
            btn.grid(row=0, column=col); col += 1
            w["tbtns"].append(btn)
            return btn

        def edge_btn(which, direction):
            kind = "rising" if which == "start" else "falling"
            where = "the sound starts" if which == "start" else "the sound has died away"
            word = "previous" if direction < 0 else "next"
            glyph = {("start", -1): "\u2196", ("start", 1): "\u2197",
                     ("end", -1): "\u2199", ("end", 1): "\u2198"}[(which, direction)]
            btn = time_btn(glyph, lambda mid=mark["id"], wh=which, d=direction: self._snap_edge(mid, wh, d),
                           f"Set {which.capitalize()} to the {word} {kind} edge in the audio ({where})\n"
                           f"again: the one {'before' if direction < 0 else 'after'} that\n"
                           "Looks in the vocals stem (if separated); Shift+click: the full mix")
            btn.bind("<ButtonRelease-1>", lambda ev: setattr(self, "_shift_edge", bool(ev.state & SHIFT_MASK)),
                     add="+")
            register_modifier_button(btn, ("shift",))
            w[f"{which}_edge{'_prev' if direction < 0 else ''}"] = btn

        for which in ("start", "end"):
            lbl = tk.Label(f, text=which.capitalize(), bg=normal_bg, fg=contrast_fg(normal_bg))
            lbl.grid(row=0, column=col, padx=(6, 2)); col += 1
            w["labels"].append(lbl)
            # earlier: to the left of the box (farthest-reaching first)
            if which == "start":
                edge_btn("start", -1)
                w["start_rsnap"] = time_btn("[", lambda mid=mark["id"]: self._snap_region(mid, "start"),
                                            "Set Start to the start of its stem region\n(again: the region before)")
                w["start_snap"] = time_btn("\u21e4", lambda mid=mark["id"]: self._snap(mid, "start"),
                                           "Set Start to the end of the previous mark (0:00 if none)")
            else:
                edge_btn("end", -1)
            time_btn("\u2212", lambda mid=mark["id"], wh=which: self._nudge(mid, wh, -1),
                     f"{which.capitalize()} earlier by the Step", repeat=True)
            e = _style_entry(tk.Entry(f, width=11, justify="right"))
            e.grid(row=0, column=col); col += 1
            e.bind("<Return>", lambda ev, mid=mark["id"], wh=which: self._commit_time(mid, wh))
            e.bind("<KP_Enter>", lambda ev, mid=mark["id"], wh=which: self._commit_time(mid, wh))
            e.bind("<FocusOut>", lambda ev, mid=mark["id"], wh=which: self._commit_time(mid, wh))
            e.bind("<Escape>", lambda ev, mid=mark["id"]: self._revert(mid))
            e.bind("<FocusIn>", lambda ev, mid=mark["id"]: self.ctl.select_mark(mid, from_panel=True))
            e.bind("<FocusIn>", lambda ev, ent=e: self._select_all_later(ent), add="+")
            e.bind("<KeyRelease>", lambda ev, mid=mark["id"], fld=e: self._note_pending(mid, fld), add="+")
            e.bind("<FocusIn>", lambda ev, fld=e: self._remember_text(fld), add="+")
            e.bind("<Tab>", lambda ev, mid=mark["id"], key=which: self.focus_adjacent_field(mid, key, 1))
            for seq in ("<Shift-Tab>", "<ISO_Left_Tab>"):
                e.bind(seq, lambda ev, mid=mark["id"], key=which: self.focus_adjacent_field(mid, key, -1))
            w[which] = e
            # later: to the right of the box, then @
            time_btn("+", lambda mid=mark["id"], wh=which: self._nudge(mid, wh, 1),
                     f"{which.capitalize()} later by the Step", repeat=True)
            if which == "start":
                edge_btn("start", 1)
            else:
                w["end_snap"] = time_btn("\u21e5", lambda mid=mark["id"]: self._snap(mid, "end"),
                                         "Set End to the start of the next mark (end of audio if none)")
                w["end_rsnap"] = time_btn("]", lambda mid=mark["id"]: self._snap_region(mid, "end"),
                                          "Set End to the end of its stem region\n(again: the region after)")
                edge_btn("end", 1)
            w[f"{which}_at"] = time_btn("@", lambda mid=mark["id"], wh=which: self._to_cursor(mid, wh),
                                        f"Set {which.capitalize()} to the @cursor")
            if which == "start":
                join = small_btn(JOIN_TEXT[self.join_mode], self._cycle_join)
                join.configure(width=JOIN_BTN_WIDTH, anchor="w")
                join.grid(row=0, column=col, padx=(4, 8)); col += 1
                _Tip(join, "When Start changes (-/+, typed, @, [, \u21e4, \u2196/\u2197), the previous card\n"
                           "ends right there:\n"
                           "  none \u2014 never\n"
                           "  group \u2014 only if the two cards were touching\n"
                           "  all \u2014 always (a gap closes)\n"
                           "Click to switch. Shared by all cards.")
                w["join"] = join
            else:
                rest = small_btn(REST_TEXT[self.rest_mode], self._cycle_rest)
                rest.configure(width=REST_BTN_WIDTH, anchor="w")
                rest.grid(row=0, column=col, padx=(4, 0)); col += 1
                _Tip(rest, "When End changes (-/+, typed, @, ], \u2199/\u2198), also move:\n"
                           "  none \u2014 nothing else\n"
                           "  group \u2014 the later cards up to the first gap\n"
                           "  all \u2014 every later card in this track\n"
                           "Click to switch. Shared by all cards.")
                w["rest"] = rest

        filler_col = col
        f.grid_columnconfigure(filler_col, weight=1)
        col += 1
        voice = tk.Menubutton(f, text=voice_button_text(mark.get("voices"), mark.get("label")), bg=BTN_BG, fg=FG,
                              activebackground=BTN_HOVER_BG, activeforeground=FG, relief="flat", bd=1,
                              highlightthickness=0, padx=4, pady=0, cursor="hand2", takefocus=0)
        voice_menu = tk.Menu(voice, tearoff=False, bg=MENU_BG, fg=MENU_FG, activebackground=MENU_ACTIVE_BG,
                             activeforeground=MENU_FG, selectcolor=MENU_FG)
        voice.configure(menu=voice_menu)
        voice_menu.configure(postcommand=lambda mid=mark["id"], m=voice_menu: self._fill_voice_menu(mid, m))
        voice.grid(row=0, column=col, padx=2); col += 1
        _Tip(voice, "Voices this card belongs to (any number)\nNew voice... adds one on the fly")
        w["voice"], w["voice_menu"] = voice, voice_menu
        split = tk.Menubutton(f, text="Split \u25be", bg=BTN_BG, fg=FG, activebackground=BTN_HOVER_BG,
                              activeforeground=FG, relief="flat", bd=1, highlightthickness=0, padx=4, pady=0,
                              cursor="hand2", takefocus=0)
        split_menu = tk.Menu(split, tearoff=False, bg=MENU_BG, fg=MENU_FG, activebackground=MENU_ACTIVE_BG,
                             activeforeground=MENU_FG)
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
        t.estimate_px = self._card_width()
        t.max_lines = getattr(self, "_field_cap", None) or self.max_field_lines()
        t.grid(row=1, column=0, columnspan=ncols, sticky="ew", pady=(3, 0))
        t.bind("<Return>", lambda ev, mid=mark["id"]: (self._commit_text(mid), "break")[1])
        t.bind("<KP_Enter>", lambda ev, mid=mark["id"]: (self._commit_text(mid), "break")[1])
        t.bind("<Shift-Return>", lambda ev: None)     # Shift+Enter: a line break in the text
        t.bind("<FocusOut>", lambda ev, mid=mark["id"]: self._commit_text(mid))
        t.bind("<Escape>", lambda ev, mid=mark["id"]: self._revert(mid))
        t.bind("<FocusIn>", lambda ev, mid=mark["id"]: self.ctl.select_mark(mid, from_panel=True))
        t.bind("<FocusIn>", lambda ev, ent=t: self._select_all_later(ent), add="+")
        t.bind("<KeyRelease>", lambda ev, mid=mark["id"], fld=t: self._note_pending(mid, fld), add="+")
        t.bind("<FocusIn>", lambda ev, fld=t: self._remember_text(fld), add="+")
        t.bind("<Tab>", lambda ev, mid=mark["id"]: self.focus_adjacent_field(mid, "text", 1))
        for seq in ("<Shift-Tab>", "<ISO_Left_Tab>"):
            t.bind(seq, lambda ev, mid=mark["id"]: self.focus_adjacent_field(mid, "text", -1))
        w["text"] = t
        # Per-word syllables / time: a hover tip (computed only when shown),
        # a right-click menu and Alt+arrow keys to adjust.
        t.bind("<Motion>", lambda ev, mid=mark["id"]: self._schedule_word_tip(mid, ev), add="+")
        t.bind("<Leave>", lambda ev: self._hide_word_tip(), add="+")
        t.bind("<KeyPress>", lambda ev: self._hide_word_tip(), add="+")
        t.bind("<Button-3>", lambda ev, mid=mark["id"]: self._word_menu(mid, ev))
        for seq, syl, sec in (("<Alt-Up>", 1, 0), ("<Alt-Down>", -1, 0), ("<Alt-Right>", 0, 1), ("<Alt-Left>", 0, -1)):
            t.bind(seq, lambda ev, mid=mark["id"], a=syl, b=sec: self._adjust_at_cursor(mid, a, b))

        # Ctrl+Z / Ctrl+Y in any card field: apply what's typed, then
        # undo/redo the marks (Entry widgets have no undo of their own).
        for entry in (w["start"], w["end"], t):
            for seq in ("<Control-z>", "<Control-Z>"):
                entry.bind(seq, lambda ev, mid=mark["id"]: self._undo_redo(mid, "undo"))
            for seq in ("<Control-y>", "<Control-Y>", "<Control-Shift-z>", "<Control-Shift-Z>"):
                entry.bind(seq, lambda ev, mid=mark["id"]: self._undo_redo(mid, "redo"))


        for widget in [f] + list(f.winfo_children()):
            if not isinstance(widget, tk.Entry):
                widget.bind("<Button-1>", lambda ev, mid=mark["id"]: self.ctl.select_mark(mid, from_panel=True),
                            add="+")
        self._forward_wheel(f)
        return w

    def _forward_wheel(self, frame):
        """Embedded widgets swallow the mouse wheel; pass it to the Text
        (and keep the line-number gutter in step)."""
        def wheel(ev):
            target = self.canvas if getattr(self, "list", None) is not None and self.mode == "track" else self.text
            if getattr(ev, "num", None) == 4 or getattr(ev, "delta", 0) > 0:
                target.yview_scroll(-WHEEL_UNITS, "units")
            else:
                target.yview_scroll(WHEEL_UNITS, "units")
            return "break"
        for widget in [frame] + list(frame.winfo_children()):
            for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                widget.bind(seq, wheel, add="+")

    def _card_width(self) -> int:
        """The cards' text width: the card list's width less a
        margin; a guess while the panel isn't laid out yet."""
        return max(300, self._list_width() - 12)

    CARD_OVERHEAD_PX = 110     # a card's height apart from its text field's lines (+ margin)

    def max_field_lines(self) -> int:
        """How many lines a card's text field may grow to: so that the
        whole card always fits inside the panel's visible height. A card
        (an embedded window) taller than the text widget's view sends Tk's
        text layout into a loop -- the hang on switching to the track with
        one long label, whose card had grown to 7-8 lines."""
        height = self._list_height()
        try:
            import tkinter.font as tkfont
            line_px = int(_field_font().metrics("linespace")) + 1
        except (tk.TclError, TypeError, ValueError, AttributeError, ImportError):
            line_px = 18
        fits = max(1, (height - self.CARD_OVERHEAD_PX) // max(1, line_px))
        if len(self.order) > 1:
            return max(1, min(MULTI_CARD_LINES, fits))
        return max(1, min(WrapField.MAX_LINES, fits))

    def _apply_field_cap(self):
        """The panel's height changed: re-cap every card's text field."""
        cap = self.max_field_lines()
        if cap == getattr(self, "_field_cap", None):
            return
        self._field_cap = cap
        crumb(f"panel card text cap {cap} lines")
        for card in self.cards.values():
            field = card.get("text")
            if field is None:
                continue
            field.max_lines = cap
            try:
                if int(field.widget.cget("height") or 1) > cap:
                    field.widget.configure(height=cap)
                else:
                    field.fit()
            except (tk.TclError, TypeError, ValueError, AttributeError):
                pass

    def _focused(self):
        try:
            return self.text.focus_get()
        except (KeyError, tk.TclError):  # focus_get can fail on some popups
            return None

    def _set_entry(self, entry, value: str) -> None:
        """Show a mark's value in a card field. A focused field is only
        left alone if the user has typed something into it: if it still
        shows what was last put there (e.g. the focus stayed in End while
        its -/+ buttons were clicked -- they don't take the focus), it's
        updated too; otherwise it kept the old time, and leaving the field
        later "committed" that old time, undoing the buttons' change."""
        focused = self._focused()
        if focused is entry or focused is getattr(entry, "widget", None):
            try:
                typed = entry.get()
            except tk.TclError:
                return
            if typed != getattr(entry, "_shown", typed + "\0"):
                return False  # don't clobber what the user is typing
        if entry.get() != value:
            entry.delete(0, "end")
            entry.insert(0, value)
        try:
            entry._shown = value
        except AttributeError:
            pass
        return True

    def _update(self, track, marks, force: bool = False) -> None:
        t0 = time.monotonic()
        self._update_inner(track, marks, force)
        ms = 1000 * (time.monotonic() - t0)
        if ms >= 20:
            crumb(f"panel._update {len(marks)} cards {ms:.0f} ms")

    def _update_inner(self, track, marks, force: bool = False) -> None:
        # Called on every waveform render (10x/s during playback): skip
        # the widget work when nothing visible has changed.
        sel_ids = (self.ctl.selected_mark_ids() if hasattr(self.ctl, "selected_mark_ids")
                   else [self.ctl.selected_mark_id()])
        sig = (track and track.get("name"), self.ctl.selected_mark_id(), tuple(sel_ids),
               tuple(getattr(self.ctl, "voices", ())),
               bool(getattr(self.ctl, "regions", None)),
               getattr(self.ctl, "_play_state", None), getattr(self.ctl, "_play_mark_id", None),
               getattr(self.ctl, "_loop", False),
               tuple((m["id"], m["start"], m.get("end"), m.get("label"), tuple(m.get("voices") or ()))
                     for m in marks))
        if not force and sig == getattr(self, "_last_sig", None):
            return
        self._last_sig = sig
        if self._header_label is not None and track:
            try:
                self._header_label.configure(text=self._header_text(track, marks))
            except tk.TclError:
                pass
        box = getattr(self, "_voice_filter_box", None)
        if box is not None:
            try:
                box.configure(values=[SHOW_ALL] + list(getattr(self.ctl, "voices", [])) + [ALL_VOICES])
            except tk.TclError:
                pass
        selected = self.ctl.selected_mark_id()
        has_regions = bool(getattr(self.ctl, "regions", None))
        n = len(marks)
        for i, m in enumerate(marks):
            card = self.cards.get(m["id"])
            if card is None:
                continue
            try:
                # Only touch what changed: the number / last-card state, and
                # the card's content -- a selection change or one edit
                # repaints one or two cards, not all of them.
                place = (i, i == n - 1)
                if force or card.get("place") != place:
                    card["place"] = place
                    card["num"].configure(text=f"#{i + 1}")
                    card["merge"].configure(state="disabled" if i == n - 1 else "normal")
                is_range = m["type"] == "range" and m.get("end") is not None
                state = self.ctl.mark_play_state(m["id"])
                content = (m["start"], m["end"] if is_range else None, m.get("label"),
                           tuple(m.get("voices") or ()), m["id"] == selected, m["id"] == self.playing_mid,
                           state, has_regions)
                if not force and card.get("content") == content:
                    continue
                shown = [self._set_entry(card["start"], th.format_time_ms(m["start"])),
                         self._set_entry(card["end"], th.format_time_ms(m["end"]) if is_range else ""),
                         self._set_entry(card["text"], m.get("label") or "")]
                # a field left alone while being typed in is filled in on a later pass
                card["content"] = content if all(x is not False for x in shown) else None
                vtext = voice_button_text(m.get("voices"), m.get("label"))
                if card["voice"].cget("text") != vtext:
                    card["voice"].configure(text=vtext)
                glyph = PAUSE_GLYPH if state == "playing" else PLAY_GLYPH
                if card["play"].cget("text") != glyph:
                    card["play"].configure(text=glyph)
                rstate = "normal" if has_regions else "disabled"
                for key in ("start_rsnap", "end_rsnap"):
                    if card[key].cget("state") != rstate:
                        card[key].configure(state=rstate)
                bg = self._card_bg(selected=(m["id"] == selected or m["id"] in sel_ids),
                                   playing=(m["id"] == self.playing_mid))
                if card["frame"].cget("bg") != bg:
                    self._paint(card, bg)
            except tk.TclError:
                pass

    def _card_bg(self, selected: bool, playing: bool = False) -> str:
        """Cards use the same colors as the track's marks on the waveform:
        the track color as drawn for its marks, or the selection color for
        the selected mark -- and green for the one the playhead is in."""
        if playing:
            return CARD_PLAY_BG
        if selected:
            try:
                return th.blend_color(getattr(self.ctl, "SELECTION_COLOR", "#ffe066"), 0.45, CARD_DARK_BASE)
            except (ValueError, TypeError):
                return CARD_SEL_BG
        track = self.ctl.track_by_id(self.track_id) if self.track_id else None
        if not track:
            return CARD_BG
        try:
            return th.blend_color(track.get("color", "#888888"), 0.25, CARD_DARK_BASE)
        except (ValueError, TypeError):
            return CARD_BG

    def _paint(self, card, bg):
        """Card background (selection / error flash). Buttons and entries
        keep their own colors; label text flips dark/light for contrast."""
        card["frame"].configure(bg=bg)
        fg = contrast_fg(bg)
        for btn in card.get("tbtns", []):
            try:
                btn.configure(bg=bg, activebackground=bg, fg=fg, activeforeground=fg)
                btn._rest_bg, btn._mod_normal_fg = bg, fg
            except tk.TclError:
                pass
        for child in card.get("labels", []):
            try:
                child.configure(bg=bg)
                if isinstance(child, tk.Label):
                    child.configure(fg=fg)
                elif isinstance(child, tk.Checkbutton):
                    child.configure(fg=fg, activebackground=bg, activeforeground=fg)
            except tk.TclError:
                pass

    def set_playing_mark(self, mid):
        """While playing: light up the card the playhead is in (None: no
        card) and scroll it into view."""
        if mid == self.playing_mid:
            return
        old, self.playing_mid = self.playing_mid, mid
        selected = self.ctl.selected_mark_id()
        for m in (old, mid):
            card = self.cards.get(m) if m else None
            if card is not None:
                try:
                    self._paint(card, self._card_bg(selected=(m == selected), playing=(m == mid)))
                except tk.TclError:
                    pass
        card = self.cards.get(mid) if mid else None
        if card is not None:
            crumb("panel see playing")
            try:
                i = self.order.index(mid)
                ahead = self.order[min(len(self.order) - 1, i + PLAY_LOOKAHEAD_CARDS)]
                self._see(ahead)                       # what's coming up next...
                self._see(mid)                         # ...without losing the current card
            except (tk.TclError, ValueError):
                pass

    def scroll_to_selected(self):
        self._scroll_to_selected()

    def _scroll_to_selected(self):
        mid = self.ctl.selected_mark_id()
        card = self.cards.get(mid)
        if card is None:
            return
        crumb("panel see selected")
        self._see(mid)

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
            card[key]._shown = value
        self._focus_list()
        return "break"

    # ------------------------------------------------------------------ edits
    def _time_limit(self) -> float:
        """Latest time a mark may reach (10% past the end of the audio)."""
        limit = getattr(self.ctl, "max_mark_time", None)
        if callable(limit):
            return limit()
        return self.ctl.audio_duration or float("inf")

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
        limit = self._time_limit()
        if value > limit:
            value = limit  # typed past the limit (10% past the end of the audio): use the limit
            if self._focused() is card[which]:
                card[which].delete(0, "end")
                card[which].insert(0, th.format_time_ms(value))
        is_range = mark["type"] == "range" and mark.get("end") is not None
        current = mark["start"] if which == "start" else (mark["end"] if is_range else None)
        if current is not None and abs(value - current) < 0.0005:
            return
        if which == "start":
            ok = self._set_start(mid, value)
        else:
            ok = self._set_end(mid, value)
        if not ok:
            self._flash_bad(mid)

    def _set_start(self, mid, value):
        """Change a card's Start -- with "join" on, the previous card in
        the track then ends right there."""
        mark = self.ctl.mark_by_id(mid)
        if mark is None:
            return False
        if self.join_mode != "off":
            return self.ctl.set_mark_start_joined(mid, value, mode=self.join_mode)
        is_range = mark["type"] == "range" and mark.get("end") is not None
        return self.ctl.set_mark_times(mid, value, mark["end"] if is_range else None)

    def _cycle_join(self):
        """The 3-state <Join button: off -> group -> all -> off."""
        self.set_join_mode(JOIN_MODES[(JOIN_MODES.index(self.join_mode) + 1) % len(JOIN_MODES)])

    def set_join_mode(self, mode):
        self.join_mode = mode if mode in JOIN_MODES else "off"
        for card in self.cards.values():
            btn = card.get("join")
            if btn is not None:
                try:
                    btn.configure(text=JOIN_TEXT[self.join_mode])
                except tk.TclError:
                    pass

    def _set_end(self, mid, value, allow_shift=True):
        """Change a card's End -- with "shift rest" on, the later marks in
        the track move by the same amount."""
        mark = self.ctl.mark_by_id(mid)
        if mark is None:
            return False
        if allow_shift and self.rest_mode != "off":
            return self.ctl.set_mark_end_shifting(mid, value, mode=self.rest_mode)
        return self.ctl.set_mark_times(mid, mark["start"], value)

    def _pending_fields(self, mid):
        """The fields of one card whose text differs from its mark."""
        card, mark = self.cards.get(mid), self.ctl.mark_by_id(mid)
        if not card or not mark:
            return []
        is_range = mark["type"] == "range" and mark.get("end") is not None
        committed = {"text": (mark.get("label") or "").strip(),
                     "start": th.format_time_ms(mark["start"]),
                     "end": th.format_time_ms(mark["end"]) if is_range else ""}
        out = []
        for key, value in committed.items():
            try:
                typed = card[key].get().strip()
            except (tk.TclError, KeyError):
                continue
            if key == "text":
                changed = typed != value
            else:
                parsed = th.parse_time(typed) if typed else None
                was = mark["start"] if key == "start" else (mark["end"] if is_range else None)
                changed = typed != value and not (parsed is not None and was is not None
                                                  and abs(parsed - was) < 0.0005)
            if changed:
                out.append(key)
        return out

    def _remember_text(self, field):
        try:
            field._last_text = field.get()
        except (tk.TclError, AttributeError):
            pass

    def _note_pending(self, mid, field=None):
        """Typing in a card: the tab shows unsaved changes right away (and
        auto-save counts from now) -- whenever the field's text changed at
        all, even after an auto-save has already applied earlier typing."""
        changed = False
        if field is not None:
            try:
                now = field.get()
                changed = now != getattr(field, "_last_text", now)
                field._last_text = now
            except (tk.TclError, AttributeError):
                pass
        if changed or self._pending_fields(mid):
            mark_dirty = getattr(getattr(self.ctl, "tab", None), "mark_dirty", None)
            if callable(mark_dirty):
                mark_dirty()

    def has_pending(self):
        return any(self._pending_fields(mid) for mid in list(self.cards))

    def commit_pending(self):
        """Before saving: apply what's typed in the cards. A time field
        still being typed in (it has the focus) is left alone, so a half-
        typed time isn't applied; its tab stays unsaved (see
        waveform_tab.save_marks_now)."""
        focused = self._focused()
        for mid in list(self.cards):
            fields = self._pending_fields(mid)
            if not fields:
                continue
            card = self.cards.get(mid)
            if "text" in fields:
                self._commit_text(mid)
            for which in ("start", "end"):
                if which in fields and card is not None and card[which] is not focused:
                    self._commit_time(mid, which)

    def focus_adjacent_field(self, mid, key, direction):
        """Tab / Shift+Tab in a card field: the same field (text, Start or
        End) of the next / previous card. Leaving the field commits it, as
        usual."""
        if mid not in self.order:
            return "break"
        i = self.order.index(mid) + direction
        if not 0 <= i < len(self.order):
            return "break"
        target = self.cards.get(self.order[i])
        if target is None:
            return "break"
        field = target.get(key)
        self._see(self.order[i])
        try:
            field.focus_set()
        except (tk.TclError, AttributeError):
            pass
        return "break"

    def select_adjacent_card(self, direction):
        """Up/Down while the card list has the focus (not a card field):
        select the previous/next card and scroll it into view. Only the two
        cards involved are repainted (see _update)."""
        if self.mode != "track" or not self.order:
            return None
        current = self.ctl.selected_mark_id()
        if current in self.order:
            i = self.order.index(current) + direction
            if not 0 <= i < len(self.order):
                return "break"
        else:
            i = 0 if direction > 0 else len(self.order) - 1
        self.ctl.select_mark(self.order[i], from_panel=True)
        self._scroll_to_selected()
        return "break"

    def set_rest_mode(self, mode):
        self.rest_mode = mode if mode in REST_MODES else "off"
        for card in self.cards.values():
            btn = card.get("rest")
            if btn is not None:
                try:
                    btn.configure(text=REST_TEXT[self.rest_mode])
                except tk.TclError:
                    pass

    def _cycle_rest(self):
        """The 3-state rest button: off -> to gap -> all -> off."""
        self.set_rest_mode(REST_MODES[(REST_MODES.index(self.rest_mode) + 1) % len(REST_MODES)])

    def _snap_edge(self, mid, which, direction=1, use_vocals=None):
        """Start -> foot of the next (direction 1) / previous (-1) rising
        edge; End -> bottom of the next / previous falling edge. In the
        vocals stem, or with Shift+click the full mix."""
        if use_vocals is None:
            use_vocals, self._shift_edge = not self._shift_edge, False
        self._commit_all(mid)
        mark = self.ctl.mark_by_id(mid)
        if not mark:
            return
        is_range = mark["type"] == "range" and mark.get("end") is not None
        if which == "start":
            t = self.ctl.rise_time(mark["start"], use_vocals=use_vocals, direction=direction)
            ok = t is not None and (not is_range or t <= mark["end"] - th.MIN_RANGE) and self._set_start(mid, t)
        else:
            base = mark["end"] if is_range else mark["start"]
            t = self.ctl.edge_time(base, "fall", use_vocals=use_vocals, direction=direction)
            ok = t is not None and t >= mark["start"] + th.MIN_RANGE and self._set_end(mid, t)
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
        duration = self._time_limit()
        is_range = mark["type"] == "range" and mark.get("end") is not None
        if which == "start":
            hi = (mark["end"] - th.MIN_RANGE) if is_range else duration
            new = min(max(0.0, mark["start"] + step), hi)
            if abs(new - mark["start"]) < 1e-9:
                return  # at the limit
            ok = self._set_start(mid, new)
        else:
            base = mark["end"] if is_range else mark["start"]
            new = min(max(mark["start"] + th.MIN_RANGE, base + step), duration)
            if is_range and abs(new - mark["end"]) < 1e-9:
                return  # at the limit
            if not is_range and direction < 0:
                return  # a point has no end to shrink
            ok = self._set_end(mid, new)
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
            ok = self._set_start(mid, t)
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
            ok = t is not None and self._set_start(mid, t)
        else:
            base = mark["end"] if is_range else mark["start"]
            t = self.ctl.region_boundary(base, 1)
            ok = t is not None and self._set_end(mid, t)
        if not ok:
            self._flash_bad(mid)

    def _toggle_play(self, mid):
        loop = getattr(self, "_shift_on_play", False)
        resume = getattr(self, "_ctrl_on_play", False)
        self._shift_on_play = self._ctrl_on_play = False
        self._commit_all(mid)
        self.ctl.toggle_mark_play(mid, loop=loop, resume=resume)

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
        target = self.canvas if getattr(self, "list", None) is not None else self.text
        try:
            target.focus_set()      # FocusOut on the card field commits it
        except tk.TclError:
            pass
        if self.track_id:
            self.ctl.select_track_only(self.track_id)
        return "break" if event is not None and event.widget in (self.text, target) else None

    def _delete(self, mid):
        """Delete this card's mark; the next card (or the previous one, if
        this was the last) becomes the selected card."""
        self._focus_list()  # this card is about to go away
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
            ok = self._set_start(mid, pos)
        else:
            ok = self._set_end(mid, pos)
        if not ok:
            self._flash_bad(mid)

    def _undo_redo(self, mid, which):
        self._commit_all(mid)
        self._focus_list()  # the card may be rebuilt; don't leave focus in it
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
        pos = self.ctl.cursor_position()
        is_range = mark["type"] == "range" and mark.get("end") is not None
        at_ok = is_range and pos is not None and mark["start"] + th.MIN_RANGE <= pos <= mark["end"] - th.MIN_RANGE
        at_label = (f"Split at @cursor ({th.format_time_ms(pos)})" if at_ok
                    else "Split at @cursor (place it inside this card first)")
        menu.add_command(label=at_label, state="normal" if at_ok else "disabled",
                         command=lambda: self._split(mid, how="time"))
        try:
            ins = int(insert)
        except (TypeError, ValueError):
            ins = -1
        text_ok = 0 < ins < len(label) and label[:ins].strip() and label[ins:].strip()
        menu.add_command(label="Split at text cursor" + (f" (before \u201c{label[ins:].split()[0][:15]}\u201d)"
                                                          if text_ok else " (click in the text first)"),
                         state="normal" if text_ok else "disabled", command=lambda: self._split(mid, how="text"))
        menu.add_command(label="Split in half", state="normal" if (is_range or n_words >= 2) else "disabled",
                         command=lambda: self._split(mid, how="half"))
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

    def _split(self, mid, how="time"):
        """how: "time" = at the @cursor, "text" = at the text cursor,
        "half" = in the middle (by word weight)."""
        card = self.cards.get(mid)
        if not card:
            return
        ctx = getattr(self, "_split_ctx", None) or {}
        text_index = None
        if how == "text":
            try:
                text_index = ctx["insert"] if ctx.get("mid") == mid else card["text"].index("insert")
                text_index = int(text_index)
            except (tk.TclError, TypeError, ValueError, KeyError):
                text_index = None
        self._split_ctx = None
        self._commit_all(mid)
        at_time = self.ctl.cursor_position() if how == "time" else -1.0   # -1: outside -> middle
        if not self.ctl.split_mark_by_id(mid, text_index=text_index, at_time=at_time):
            self._flash_bad(mid)

    def _merge_next(self, mid):
        """Merge with the next card shown (the Show: filter hides others)."""
        self._commit_all(mid)
        mark = self.ctl.mark_by_id(mid)
        pool = self.visible_marks(mark.get("track_id")) if mark else None
        if not self.ctl.merge_mark_by_id(mid, direction=1, pool=pool):
            self._flash_bad(mid)

    # ------------------------------------------------------------------ voices
    def _fill_voice_menu(self, mid, menu):
        self._commit_all(mid)
        self.ctl.fill_voice_menu(menu, mid)

    # ------------------------------------------------------------------ syllables / time per word
    def _offset_at(self, field, x, y):
        """Character offset in a card's text at a mouse position."""
        try:
            index = field.widget.index(f"@{int(x)},{int(y)}")
            return _count(field.widget.count("1.0", index, "chars"))
        except (tk.TclError, AttributeError, TypeError, ValueError):
            return None

    def word_info(self, mid, offset):
        """word_timings() entry for the word at this offset of the card's
        (committed) text, or None."""
        mark = self.ctl.mark_by_id(mid)
        if mark is None or offset is None:
            return None
        label = mark.get("label") or ""
        target = th.word_at(label, offset)
        if target is None or not target["word"]:
            return None
        for info in th.word_timings(mark):
            if info["span"] == target["span"]:
                return info
        return None

    def word_tip_text(self, mid, offset):
        info = self.word_info(mid, offset)
        return describe_word(info) if info else None

    def _schedule_word_tip(self, mid, event):
        """Restart the hover delay; nothing is computed until it fires."""
        self._hide_word_tip()
        card = self.cards.get(mid)
        if card is None:
            return
        x, y = getattr(event, "x", 0), getattr(event, "y", 0)
        xr, yr = getattr(event, "x_root", x), getattr(event, "y_root", y)
        try:
            self._word_tip_after = self.text.after(WORD_TIP_DELAY_MS,
                                                   lambda: self._show_word_tip(mid, x, y, xr, yr))
        except tk.TclError:
            self._word_tip_after = None

    def _show_word_tip(self, mid, x, y, x_root, y_root):
        self._word_tip_after = None
        card = self.cards.get(mid)
        if card is None:
            return
        # Typed but not yet committed text: nothing to describe reliably.
        if card["text"].get().strip() != (self.ctl.mark_by_id(mid) or {}).get("label", "").strip():
            return
        text = self.word_tip_text(mid, self._offset_at(card["text"], x, y))
        if not text:
            return
        try:
            tip = tk.Toplevel(self.text)
            tip.wm_overrideredirect(True)
            tip.wm_geometry(f"+{int(x_root) + 12}+{int(y_root) + 16}")
            tk.Label(tip, text=text, background=TIP_BG, foreground=TIP_FG, relief="solid", borderwidth=1,
                     justify="left", font=("TkDefaultFont", 8), padx=4, pady=2).pack()
            self._word_tip = tip
        except (tk.TclError, TypeError):
            self._word_tip = None

    def _hide_word_tip(self):
        if self._word_tip_after is not None:
            try:
                self.text.after_cancel(self._word_tip_after)
            except (tk.TclError, ValueError):
                pass
            self._word_tip_after = None
        if self._word_tip is not None:
            try:
                self._word_tip.destroy()
            except tk.TclError:
                pass
            self._word_tip = None

    def adjust_word(self, mid, offset, syllables=0, seconds=0.0, clear=False):
        """Change the {+n} / {+n s} adjustment of the word at offset in this
        card's text (one undo step); keeps the text cursor after that word.
        Returns True if the text changed."""
        self._hide_word_tip()
        self._commit_text(mid)
        mark = self.ctl.mark_by_id(mid)
        if mark is None or offset is None:
            return False
        label = mark.get("label") or ""
        result = th.adjust_word(label, offset, syllables=syllables, seconds=seconds, clear=clear)
        if result is None or result[0] == label:
            return False
        new_label, (_a, b) = result
        if not self.ctl.set_mark_label(mid, new_label):
            return False
        card = self.cards.get(mid)
        if card is not None:
            try:
                card["text"].delete(0, "end")
                card["text"].insert(0, self.ctl.mark_by_id(mid).get("label") or "")
                card["text"]._shown = card["text"].get()
                card["text"].icursor(min(b, len(card["text"].get())))
            except tk.TclError:
                pass
        return True

    def _adjust_at_cursor(self, mid, syl_dir, time_dir):
        card = self.cards.get(mid)
        if card is None:
            return "break"
        try:
            offset = card["text"].index("insert")
        except tk.TclError:
            return "break"
        self.adjust_word(mid, offset, syllables=syl_dir, seconds=time_dir * self._step())
        return "break"

    def _word_menu(self, mid, event):
        """Right-click on a word: its syllables/time and the adjustments."""
        self._hide_word_tip()
        card = self.cards.get(mid)
        if card is None:
            return "break"
        self._commit_text(mid)
        offset = self._offset_at(card["text"], getattr(event, "x", 0), getattr(event, "y", 0))
        menu = self.build_word_menu(mid, offset)
        if menu is None:
            return "break"
        try:
            menu.tk_popup(getattr(event, "x_root", 0), getattr(event, "y_root", 0))
        finally:
            try:
                menu.grab_release()
            except tk.TclError:
                pass
        return "break"

    def build_word_menu(self, mid, offset):
        info = self.word_info(mid, offset)
        if info is None:
            return None
        step = self._step()
        menu = tk.Menu(self.text, tearoff=False, bg=MENU_BG, fg=MENU_FG, activebackground=MENU_ACTIVE_BG,
                       activeforeground=MENU_FG, disabledforeground="#777777")
        menu.add_command(label=describe_word(info).split("\n")[0], state="disabled")
        menu.add_separator()
        menu.add_command(label="One more syllable  {+1}", accelerator="Alt+\u2191",
                         command=lambda: self.adjust_word(mid, offset, syllables=1))
        menu.add_command(label="One less syllable  {-1}", accelerator="Alt+\u2193",
                         state="normal" if info["syllables"] > 0 else "disabled",
                         command=lambda: self.adjust_word(mid, offset, syllables=-1))
        menu.add_command(label=f"Longer by {step:g} s  {{{th.format_adjust_seconds(step)}}}",
                         accelerator="Alt+\u2192", command=lambda: self.adjust_word(mid, offset, seconds=step))
        menu.add_command(label=f"Shorter by {step:g} s  {{{th.format_adjust_seconds(-step)}}}",
                         accelerator="Alt+\u2190", command=lambda: self.adjust_word(mid, offset, seconds=-step))
        menu.add_separator()
        menu.add_command(label="Remove this word's adjustment",
                         state="normal" if info["syl_adj"] or info["time_adj"] else "disabled",
                         command=lambda: self.adjust_word(mid, offset, clear=True))
        self._last_word_menu = menu
        return menu
