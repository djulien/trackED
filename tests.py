#!/usr/bin/env python3
"""
Regression tests for trackED's waveform/timing features
--------------------------------------------------------
(waveform_tab.py, timing_panel.py, timing_helpers.py, audio_analysis.py,
plus the small pieces of editor_tab.py / tracked.py / utils.py they rely on.)

Same approach as the Sequence Editor's tests.py, which several of these
tests are ported from: plain Python, hand-built fake tkinter/ttk stubs so
the real logic can run without a display, and a simple check() that
prints OK/FAIL and exits non-zero on any failure.

Run:
    python3 tests.py

Needs ffmpeg on PATH for the decode/metadata tests (skipped with a note
otherwise). demucs, torch and Whisper are NOT exercised for real -- the
stem and transcription tests install small stand-in modules that mimic
their APIs, so the suite runs in seconds and needs no model downloads.
Everything is written to a temporary directory, and HOME is pointed at a
temporary directory too, so your real trackED preferences are untouched.
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile
import io
import time
import types
import wave

TMP = tempfile.mkdtemp(prefix="tracked_tests_")
os.environ["HOME"] = os.environ["USERPROFILE"] = os.path.join(TMP, "home")
os.makedirs(os.environ["HOME"], exist_ok=True)

FAILURES = []
PASS_COUNT = 0


def check(condition, message):
    global PASS_COUNT
    if condition:
        PASS_COUNT += 1
        print(f"  OK: {message}")
    else:
        FAILURES.append(message)
        print(f"  FAIL: {message}")


# ---------------------------------------------------------------------------
# Fake tkinter -- just enough widget behavior for the controller and the
# timing panel. Entry keeps real text + an insert cursor; Canvas records
# every item it draws; widgets record bindings so tests can fire them.
# ---------------------------------------------------------------------------

AFTERS = []          # callbacks queued via widget.after(); run by run_afters()
FOCUS = {"w": None}


class TclError(Exception):
    pass


class FakeVar:
    def __init__(self, master=None, value=""):
        self._v = value
        self._traces = []

    def get(self):
        return self._v

    def set(self, v):
        self._v = v
        for fn in self._traces:
            fn("", "", "write")

    def trace_add(self, mode, fn):
        self._traces.append(fn)


class _Anything:
    """Returned for any widget method a test doesn't care about."""
    def __call__(self, *a, **k):
        return _Anything()

    def __getattr__(self, name):
        return _Anything()

    def __bool__(self):
        return False


class FakeWidget:
    def __init__(self, master=None, *args, **kw):
        self.master = master
        self._cfg = dict(kw)
        self._children = []
        self._binds = {}
        self._destroyed = False
        if isinstance(master, FakeWidget):
            master._children.append(self)

    # config
    def configure(self, *a, **kw):
        self._cfg.update(kw)

    config = configure

    def cget(self, key):
        if key in self._cfg:
            return self._cfg[key]
        return "#ffffff" if key in ("bg", "background") else ""

    @property
    def cursor(self):
        return self._cfg.get("cursor", "")

    # bindings
    def bind(self, seq=None, fn=None, add=None):
        if seq is None:
            return list(self._binds)
        self._binds.setdefault(seq, []).append(fn)

    def unbind(self, seq, funcid=None):
        self._binds.pop(seq, None)

    def fire(self, seq, event=None):
        out = None
        for fn in list(self._binds.get(seq, [])):
            out = fn(event or Event())
        return out

    # geometry / misc
    def pack(self, **kw): self._packed = kw
    def pack_forget(self): self._packed = None
    @property
    def packed(self):
        return getattr(self, "_packed", None) is not None
    def grid(self, **kw): self._gridded = True
    def grid_remove(self): self._gridded = False
    def grid_columnconfigure(self, *a, **k): pass
    def winfo_children(self): return list(self._children)
    def winfo_width(self): return 800
    def winfo_height(self): return 200
    def winfo_reqheight(self): return 28
    def winfo_y(self): return 4
    def winfo_rootx(self): return 0
    def winfo_rooty(self): return 0
    def winfo_toplevel(self): return self
    def winfo_pointerxy(self): return (0, 0)
    def winfo_containing(self, x, y): return None
    def winfo_exists(self): return not self._destroyed
    def update_idletasks(self): pass
    def destroy(self): self._destroyed = True
    def focus_set(self): FOCUS["w"] = self
    def focus_get(self): return FOCUS["w"]
    def bell(self): pass

    def after(self, ms, fn=None, *args):
        AFTERS.append(fn)
        return f"after#{len(AFTERS)}"

    def after_cancel(self, ident):
        pass

    def __getattr__(self, name):
        if name.startswith("_"):
            raise AttributeError(name)
        return _Anything()


class FakeTab(FakeWidget):
    """Stands in for editor_tab.EditorTab: just the dirty/title API the
    plugins call."""
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.dirty = False
        self.dirty_since = None
        self.title_refreshes = 0

    def set_line_numbers_visible(self, visible):
        self._line_numbers_shown = bool(visible)

    def mark_dirty(self):
        if not self.dirty:
            self.dirty = True
            self.dirty_since = time.monotonic()

    def mark_clean(self):
        self.dirty = False
        self.dirty_since = None

    def refresh_title(self):
        self.title_refreshes += 1


class FakeEntry(FakeWidget):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self._text = ""
        self._insert = 0

    def get(self):
        return self._text

    def insert(self, index, s):
        i = len(self._text) if index == "end" else int(index)
        self._text = self._text[:i] + s + self._text[i:]
        self._insert = i + len(s)

    def delete(self, a, b=None):
        a = int(a)
        b = len(self._text) if b in (None, "end") else int(b)
        self._text = self._text[:a] + self._text[b:]
        self._insert = min(self._insert, len(self._text))

    def index(self, which):
        return self._insert if which == "insert" else len(self._text)

    def icursor(self, i):
        self._insert = len(self._text) if i == "end" else i

    def select_range(self, a, b):
        self.selection = (a, b)

    def type_text(self, s):
        """Test helper: replace the contents as a user would."""
        self.delete(0, "end")
        self.insert(0, s)


class FakeText(FakeWidget):
    """Text widget stand-in: one string plus an insert mark and a "sel"
    tag, with indices "1.0", "end", "end-1c", "insert", "1.N" and
    "1.0 + N chars" (enough for the panel and the card text fields)."""
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self._s = ""
        self._ins = 0
        self._sel = None
        self.windows = []
        self._marks = {}          # named marks
        self._gravity = {}        # name -> "left" / "right" (default)

    @property
    def content(self):
        return [self._s]

    def _off(self, index):
        index = str(index)
        if index in ("end", "end-1c"):
            return len(self._s)
        if index == "insert":
            return self._ins
        if index in self._marks:
            return self._marks[index]
        m = re.match(r"^(.+?) \+ (\d+) chars$", index)
        if m and (m.group(1) in self._marks or " + " in m.group(1) or re.match(r"^\d+\.\d+$", m.group(1))):
            return min(len(self._s), self._off(m.group(1)) + int(m.group(2)))
        m = re.match(r"^1\.0 \+ (\d+) chars$", index)
        if m:
            return min(len(self._s), int(m.group(1)))
        m = re.match(r"^1\.(\d+)$", index)
        if m:
            return min(len(self._s), int(m.group(1)))
        return len(self._s)

    def insert(self, index, s, *tags):
        i = self._off(index)
        self._s = self._s[:i] + s + self._s[i:]
        self._ins = i + len(s)
        for name, pos in self._marks.items():
            if pos > i or (pos == i and self._gravity.get(name, "right") == "right"):
                self._marks[name] = pos + len(s)

    def index(self, index):
        return f"1.0 + {self._off(index)} chars"

    def mark_unset(self, name):
        self._marks.pop(name, None)

    def mark_gravity(self, name, gravity=None):
        if gravity is not None:
            self._gravity[name] = gravity
        return self._gravity.get(name, "right")

    def delete(self, a, b=None):
        i, j = self._off(a), self._off(b if b is not None else a)
        self._s = self._s[:i] + self._s[j:]
        for name, pos in self._marks.items():
            self._marks[name] = i if i <= pos < j else (pos - (j - i) if pos >= j else pos)
        self._ins = min(self._ins, len(self._s))
        if a == "1.0" and b in ("end", None):
            self.windows = []

    def get(self, a="1.0", b="end"):
        return self._s[self._off(a):self._off(b)]

    def count(self, a, b, *kinds):
        if "displaylines" in kinds:
            return (max(1, self._s.count("\n") + 1),)
        return (self._off(b) - self._off(a),)

    def mark_set(self, name, index):
        if name == "insert":
            self._ins = self._off(index)
        else:
            self._marks[name] = self._off(index)

    def tag_add(self, tag, a, b=None):
        if tag == "sel":
            self._sel = (self._off(a), self._off(b))

    def tag_remove(self, tag, *a):
        if tag == "sel":
            self._sel = None

    def tag_ranges(self, tag):
        if tag == "sel" and self._sel:
            return (f"1.{self._sel[0]}", f"1.{self._sel[1]}")
        return ()

    def type_text(self, s):
        self._s, self._ins = s, len(s)

    def window_create(self, index, window=None, **k):
        self.windows.append(window)
        # an embedded window takes one text position, as in Tk (a private-
        # use character per window, so window_order() can find it)
        self.insert(index, chr(0xE000 + len(self.windows) - 1))

    def window_order(self):
        """The embedded windows in text order (test helper)."""
        return [self.windows[ord(ch) - 0xE000] for ch in self._s if 0xE000 <= ord(ch) < 0xF8FF]

    def edit_modified(self, flag=None):
        return False

    def see(self, index): pass
    def yview_scroll(self, *a): pass
    def tag_configure(self, *a, **k): pass


class FakeCanvas(FakeWidget):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.items = []
        self.windows = {}         # window items: id -> {"coords": [x, y], "window": w, ...}
        self._next_win = 10000
        self.moved_to = None

    def create_window(self, x, y, window=None, **kw):
        self._next_win += 1
        self.windows[self._next_win] = {"coords": [x, y], "window": window, **kw}
        return self._next_win

    def coords(self, item, *xy):
        if item in self.windows:
            if xy:
                self.windows[item]["coords"] = list(xy)
            return self.windows[item]["coords"]
        return []

    def itemconfigure(self, item, **kw):
        if item in self.windows:
            self.windows[item].update(kw)

    def canvasy(self, y):
        return y

    def yview_moveto(self, fraction):
        self.moved_to = fraction

    def delete(self, *a):
        if a and isinstance(a[0], int) and a[0] in self.windows:
            self.windows.pop(a[0], None)
            return
        if a and a[0] != "all" and isinstance(a[0], str):
            self.items = [it for it in self.items if a[0] not in (it.get("tags") or ())]
            return
        self.items = []
        self.windows = {}

    def _add(self, kind, coords, kw):
        self.items.append({"kind": kind, "coords": coords, **kw})
        return len(self.items) - 1

    def create_line(self, *coords, **kw): return self._add("line", coords, kw)
    def create_rectangle(self, *coords, **kw): return self._add("rect", coords, kw)
    def create_text(self, *coords, **kw): return self._add("text", coords, kw)

    def bbox(self, tag):
        """Rough text extents (6 px per character), honoring the anchor."""
        if isinstance(tag, int) and 0 <= tag < len(self.items) and self.items[tag]["kind"] == "text":
            it = self.items[tag]
            x, y = it["coords"][:2]
            w = 6 * len(str(it.get("text", "")))
            anchor = it.get("anchor", "center")
            x0 = x - w if "e" in anchor else (x if "w" in anchor else x - w // 2)
            return (x0, y - 6, x0 + w, y + 6)
        return (0, 0, 10, 10)


class FakeScale(FakeWidget):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self._v = 0

    def set(self, v):
        self._v = v

    def get(self):
        return self._v


class FakeMenu(FakeWidget):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.entries = []

    def add_command(self, **k):
        self.entries.append(k)

    def add_checkbutton(self, **k):
        self.entries.append(dict(k, kind="check"))

    def add_radiobutton(self, **k):
        self.entries.append(dict(k, kind="radio"))

    def add_cascade(self, **k):
        self.entries.append(dict(k, kind="cascade"))

    def delete(self, *a):
        self.entries = []

    def invoke_label(self, label):
        """Test helper: run the entry's command, like clicking it."""
        entry = self.entry(label)
        if entry.get("kind") == "check" and entry.get("variable") is not None:
            entry["variable"].set(not entry["variable"].get())
        return entry["command"]()

    def add_separator(self): pass
    def tk_popup(self, *a): pass

    def labels(self):
        return [e["label"] for e in self.entries]

    def entry(self, label):
        return next(e for e in self.entries if e["label"] == label)


class FakeTreeview(FakeWidget):
    """ttk.Treeview stand-in: items with parent/children, values, tags,
    selection and headings."""
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.items = {}
        self.kids = {"": []}
        self._selection = []
        self.headings = {}
        self._n = 0

    def insert(self, parent, index, iid=None, text="", values=(), tags=(), open=False, **k):
        if iid is None:
            self._n += 1
            iid = f"I{self._n}"
        self.items[iid] = {"parent": parent, "text": text, "values": tuple(values), "tags": tuple(tags), "open": open}
        self.kids.setdefault(parent, []).append(iid)
        self.kids.setdefault(iid, [])
        return iid

    def delete(self, *iids):
        for iid in iids:
            for child in list(self.kids.get(iid, [])):
                self.delete(child)
            item = self.items.pop(iid, None)
            if item is not None:
                self.kids[item["parent"]].remove(iid)
            self.kids.pop(iid, None)
            if iid in self._selection:
                self._selection.remove(iid)

    def parent(self, iid):
        return self.items[iid]["parent"] if iid in self.items else ""

    def see(self, iid):
        self.seen = iid

    def get_children(self, item=""):
        return tuple(self.kids.get(item, []))

    def item(self, iid, option=None, **kw):
        if kw:
            self.items[iid].update(kw)
            return None
        return self.items[iid] if option is None else self.items[iid][option]

    def selection(self):
        return tuple(self._selection)

    def selection_set(self, items):
        if isinstance(items, str):
            items = (items,)
        self._selection = [i for i in items if i in self.items]

    def heading(self, col, text=None, command=None, **k):
        h = self.headings.setdefault(col, {})
        if text is not None:
            h["text"] = text
        if command is not None:
            h["command"] = command
        return h


class Event:
    def __init__(self, x=0, y=10, state=0, num=None, delta=None, x_root=None, y_root=None, keysym=None):
        self.x, self.y, self.state, self.num, self.delta = x, y, state, num, delta
        self.x_root = x if x_root is None else x_root
        self.y_root = y if y_root is None else y_root
        self.keysym = keysym


def install_fake_tk():
    tk = types.ModuleType("tkinter")
    for name in ("Tk", "Toplevel", "Frame", "Label", "Button", "Checkbutton", "Spinbox",
                 "Menubutton", "PhotoImage", "Scrollbar", "Listbox", "PanedWindow"):
        setattr(tk, name, FakeWidget)
    tk.Entry, tk.Text, tk.Canvas, tk.Menu = FakeEntry, FakeText, FakeCanvas, FakeMenu
    tk.Scale = FakeScale
    tk.StringVar = tk.IntVar = tk.DoubleVar = tk.BooleanVar = FakeVar
    tk.TclError = TclError
    tk.END, tk.INSERT = "end", "insert"

    ttk = types.ModuleType("tkinter.ttk")
    for name in ("Frame", "Label", "Button", "Scrollbar", "Progressbar", "Notebook", "Style",
                 "Checkbutton", "PanedWindow", "Panedwindow", "Separator", "Scale", "LabelFrame", "Menubutton"):
        setattr(ttk, name, FakeWidget)
    ttk.Entry = ttk.Combobox = ttk.Spinbox = FakeEntry
    ttk.Treeview = FakeTreeview

    messagebox = types.ModuleType("tkinter.messagebox")
    messagebox.askyesno = lambda *a, **k: True
    messagebox.askyesnocancel = lambda *a, **k: False
    messagebox.showinfo = messagebox.showerror = messagebox.showwarning = lambda *a, **k: None
    simpledialog = types.ModuleType("tkinter.simpledialog")
    simpledialog.askstring = lambda *a, **k: None
    simpledialog.askfloat = lambda *a, **k: None
    colorchooser = types.ModuleType("tkinter.colorchooser")
    colorchooser.askcolor = lambda *a, **k: (None, None)
    filedialog = types.ModuleType("tkinter.filedialog")
    filedialog.asksaveasfilename = filedialog.askopenfilename = lambda *a, **k: ""
    font = types.ModuleType("tkinter.font")
    font.Font = FakeWidget
    font.nametofont = lambda *a, **k: FakeWidget()

    for mod_name, mod in (("ttk", ttk), ("messagebox", messagebox), ("simpledialog", simpledialog),
                          ("colorchooser", colorchooser), ("filedialog", filedialog), ("font", font)):
        setattr(tk, mod_name, mod)
        sys.modules[f"tkinter.{mod_name}"] = mod
    sys.modules["tkinter"] = tk
    return tk


def run_afters(limit=2000, sleep=0.01):
    """Run queued after() callbacks (they may queue more), like a mainloop."""
    n = 0
    while AFTERS and n < limit:
        fn = AFTERS.pop(0)
        n += 1
        if fn is not None:
            fn()
        if sleep:
            time.sleep(sleep)


# ---------------------------------------------------------------------------
# Optional-library stand-ins
# ---------------------------------------------------------------------------

def install_fake_soundfile_if_missing():
    """A WAV-only soundfile stand-in, used only when the real package isn't
    installed, so the stem save/reload path can still be tested."""
    try:
        import soundfile  # noqa: F401
        return False
    except ImportError:
        pass
    import numpy as np
    sf = types.ModuleType("soundfile")

    class _Info:
        def __init__(self, frames, rate):
            self.frames, self.samplerate = frames, rate

    class SoundFile:
        def __init__(self, path):
            if not str(path).lower().endswith(".wav"):
                raise RuntimeError("fake soundfile: WAV only")
            self.w = wave.open(str(path))
            self.samplerate = self.w.getframerate()
            self.channels = self.w.getnchannels()

        def __enter__(self): return self
        def __exit__(self, *a): self.w.close()
        def seek(self, n): self.w.setpos(n)

        def read(self, n=-1, dtype="float32", always_2d=True):
            n = self.w.getnframes() if n is None or n < 0 else n
            a = np.frombuffer(self.w.readframes(n), dtype=np.int16).astype(np.float32) / 32768.0
            return a.reshape(-1, self.channels)

    def info(path):
        w = wave.open(str(path))
        return _Info(w.getnframes(), w.getframerate())

    def read(path, dtype="float32", always_2d=True):
        with SoundFile(path) as f:
            return f.read(-1), f.samplerate

    def write(path, data, rate):
        a = np.asarray(data, dtype=np.float32)
        if a.ndim == 1:
            a = a[:, None]
        w = wave.open(str(path), "wb")
        w.setnchannels(a.shape[1]); w.setsampwidth(2); w.setframerate(int(rate))
        w.writeframes((np.clip(a, -1, 1) * 32767).astype(np.int16).tobytes())
        w.close()

    sf.SoundFile, sf.info, sf.read, sf.write = SoundFile, info, read, write
    sys.modules["soundfile"] = sf
    return True


def install_fake_ml(vocal_window=(2.0, 6.0)):
    """Stand-ins for torch + demucs (vocals = the audio inside
    vocal_window, everything else = accompaniment) and faster_whisper
    (returns how many seconds of non-silent audio it was given)."""
    import numpy as np
    torch = types.ModuleType("torch")

    class T(np.ndarray):
        def cpu(self): return self
        def numpy(self): return np.asarray(self)

    torch.wrap = lambda a: np.asarray(a).view(T)
    torch.cuda = types.SimpleNamespace(is_available=lambda: False)

    class _NoGrad:
        def __enter__(self): return self
        def __exit__(self, *a): return False
    torch.no_grad = _NoGrad

    demucs = types.ModuleType("demucs")
    pretrained = types.ModuleType("demucs.pretrained")
    apply = types.ModuleType("demucs.apply")
    audio = types.ModuleType("demucs.audio")

    class Model:
        samplerate, audio_channels = 8000, 2
        sources = ["drums", "bass", "other", "vocals"]
        def eval(self): pass
        def cuda(self): pass

    pretrained.get_model = lambda name: Model()

    class AudioFile:
        def __init__(self, path): self.path = path
        def read(self, streams=0, samplerate=8000, channels=2):
            raw = subprocess.run(["ffmpeg", "-v", "error", "-i", self.path, "-ac", str(channels),
                                  "-ar", str(samplerate), "-f", "f32le", "-"], capture_output=True).stdout
            return torch.wrap(np.frombuffer(raw, dtype=np.float32).reshape(-1, channels).T.copy())
    audio.AudioFile = AudioFile

    calls = {"separations": 0}

    def apply_model(model, mix, callback=None, **kw):
        calls["separations"] += 1
        x = np.asarray(mix)[0]
        t = np.arange(x.shape[-1]) / model.samplerate
        gate = ((t >= vocal_window[0]) & (t < vocal_window[1])).astype(np.float32)
        voc, acc = x * gate, x * (1 - gate)
        if callback:
            callback({"segment_offset": x.shape[-1], "audio_length": x.shape[-1], "state": "end"})
        return torch.wrap(np.stack([acc * 0, acc * 0, acc, voc])[None])
    apply.apply_model = apply_model

    fw = types.ModuleType("faster_whisper")

    class WhisperModel:
        loads = 0
        def __init__(self, size, device="cpu", compute_type="int8"):
            WhisperModel.loads += 1
            self.size = size
        def transcribe(self, audio, **kw):
            voiced = np.count_nonzero(np.abs(audio) > 1e-4) / 16000.0
            seg = types.SimpleNamespace(text=f" sung for {voiced:.1f} seconds ", start=0.0, end=voiced)
            return iter([seg]), None
    fw.WhisperModel = WhisperModel

    sys.modules.update({"torch": torch, "demucs": demucs, "demucs.pretrained": pretrained,
                        "demucs.apply": apply, "demucs.audio": audio, "faster_whisper": fw})
    return calls, WhisperModel


class FakeEngine:
    """Playback engine stand-in that records play_segment calls."""
    def __init__(self):
        self.active = False
        self.calls = []
        self.volume = 1.0

    def set_volume(self, v):
        self.volume = v

    def load(self, path): return True

    def play_segment(self, start, duration, speed):
        self.calls.append((round(start, 3), None if duration is None else round(duration, 3)))
        self.active = True
        return True

    def stop(self): self.active = False
    def is_active(self): return self.active
    def close(self): pass


# ---------------------------------------------------------------------------
# Loading the modules under test
# ---------------------------------------------------------------------------

HERE = os.path.dirname(os.path.abspath(__file__))
HAVE_FFMPEG = shutil.which("ffmpeg") is not None and shutil.which("ffprobe") is not None


def load_modules():
    install_fake_tk()
    used_fake_sf = install_fake_soundfile_if_missing()
    if HERE not in sys.path:
        sys.path.insert(0, HERE)
    import timing_helpers as th
    import audio_analysis as aa
    import waveform_tab as wt
    th.make_playback_engine = lambda *a, **k: FakeEngine()
    return th, aa, wt, used_fake_sf


def make_media(name, seconds=10.0, freq=440, fmt="wav", extra=()):
    path = os.path.join(TMP, f"{name}.{fmt}")
    subprocess.run(["ffmpeg", "-v", "error", "-y", "-f", "lavfi", "-i", f"sine=frequency={freq}:duration={seconds}",
                    "-ac", "2", *extra, path], check=True)
    return path


def fresh_copy(src, name):
    """A separate copy of a media file, so each test gets its own cache."""
    dst = os.path.join(TMP, name + os.path.splitext(src)[1])
    shutil.copyfile(src, dst)
    return dst


def open_controller(wt, path, wait=True):
    """Run the plugin's onload() the way editor_tab does; returns
    (controller, canvas, text, tab)."""
    canvas, text, tab = FakeCanvas(FakeWidget()), FakeText(), FakeTab()
    claimed = wt.onload(path, canvas=canvas, text=text, tab=tab)
    assert claimed, "waveform_tab didn't claim the media file"
    ctl = canvas._waveform_controller
    if wait:
        run_afters()
    return ctl, canvas, text, tab


def bare_controller(wt, path, duration=100.0):
    """A controller with a fixed duration and view, without waiting on a
    real decode (for pure interaction tests, like seqed's EditorTab tests)."""
    ctl, canvas, text, tab = open_controller(wt, path, wait=False)
    AFTERS.clear()
    ctl.audio_duration = duration
    ctl.view_start, ctl.view_end = 0.0, duration
    ctl.full_peaks = [(-0.5, 0.5)] * 4000
    ctl.peaks = [(-0.5, 0.5)] * 800
    ctl.regions = []
    ctl._region_starts = []
    return ctl, canvas, text, tab


# ---------------------------------------------------------------------------
# Tests: pure helpers (several ported from the Sequence Editor's tests.py)
# ---------------------------------------------------------------------------

def test_time_formatting(th):
    print("\n-- time formatting + parsing --")
    check(th.format_time(65) == "1:05", "format_time(65) == '1:05'")
    check(th.format_time(3725) == "1:02:05", "format_time(3725) == '1:02:05'")
    check(th.format_time_ms(65.4321) == "1:05.432", "format_time_ms(65.4321) == '1:05.432'")
    check(th.format_time_ms(3725.001) == "1:02:05.001", "format_time_ms(3725.001) == '1:02:05.001'")
    check(th.parse_time("1:05.432") == 65.432, "parse_time reads m:ss.mmm")
    check(abs(th.parse_time("1:02:05.001") - 3725.001) < 1e-9, "parse_time reads h:mm:ss.mmm")
    check(th.parse_time("12.5") == 12.5, "parse_time reads plain seconds")
    check(th.parse_time("abc") is None and th.parse_time("") is None and th.parse_time("-1") is None,
          "parse_time rejects junk, empty and negative input")
    for t in (0.0, 1.234, 59.999, 61.0, 3599.5):
        check(abs(th.parse_time(th.format_time_ms(t)) - t) < 0.0006, f"format/parse round-trips {t}")


def test_rebucket_peaks(th):
    print("\n-- rebucket_peaks (zoom/pan without re-decoding) --")
    full = [(-1.0, 1.0)] * 1000
    sub = th.rebucket_peaks(full, 0.25, 0.75, 100)
    check(len(sub) == 100, "rebucket_peaks returns requested bucket count")
    check(all(tuple(p) == (-1.0, 1.0) for p in sub), "rebucket_peaks preserves values on a trivial case")
    full2 = [(i / 1000.0 - 1.0, i / 1000.0) for i in range(1000)]
    maxes = [p[1] for p in th.rebucket_peaks(full2, 0.0, 1.0, 10)]
    check(maxes == sorted(maxes), "rebucket_peaks preserves monotonic ordering when downsampling")


def test_overlap_lanes(th):
    print("\n-- overlap lane assignment --")
    lanes = th.assign_lanes([(0.0, 10.0, "a"), (5.0, 15.0, "b")])
    check(lanes["a"] != lanes["b"], "two overlapping ranges get different lanes")
    lanes = th.assign_lanes([(0.0, 10.0, "a"), (10.0, 20.0, "b")])
    check(lanes["a"] == lanes["b"], "two back-to-back (non-overlapping) ranges share a lane")
    lanes = th.assign_lanes([(0.0, 10.0, "a"), (20.0, 30.0, "b"), (5.0, 25.0, "c")])
    check(len({lanes["a"], lanes["b"], lanes["c"]}) == 2 and lanes["a"] == lanes["b"],
          "a range overlapping two separate ones only needs one extra lane")
    lanes = th.assign_lanes([(10.0, 10.0, "a"), (10.5, 10.5, "b")], epsilon=1.0)
    check(lanes["a"] != lanes["b"], "epsilon padding separates near-touching point marks")


def test_exports(th):
    print("\n-- xLights / LRC / Audacity export --")
    import xml.etree.ElementTree as ET
    marks = [
        {"start": 5.0, "end": 10.0, "label": "Chorus"},
        {"start": 0.0, "end": 2.5, "label": "Verse 1"},
        {"start": 20.0, "end": None, "label": ""},
    ]
    el = th.build_xlights_timing_element("Vocals", marks)
    effects = el.find("EffectLayer").findall("Effect")
    check(el.tag == "timing" and el.get("name") == "Vocals", "xLights root is <timing name=...>")
    check([int(e.get("starttime")) for e in effects] == [0, 5000, 20000], "xLights effects sorted, in ms")
    point = next(e for e in effects if int(e.get("starttime")) == 20000)
    check(int(point.get("endtime")) == 20001, "a point mark gets a 1 ms width in xLights")
    check(point.get("label") == th.format_time_ms(20.0), "an unlabeled mark falls back to its timestamp")
    check(all(set(e.keys()) == {"label", "starttime", "endtime"} for e in effects),
          "Effects carry exactly label/starttime/endtime, like a real xLights export")

    out = os.path.join(TMP, "_escape.xtiming")
    th.export_xlights_timing_file(out, [("A & B", [{"start": 0.0, "end": 1.0, "label": 'Say "hi" & <bye>'}])])
    root = ET.parse(out).getroot()
    check(root.tag == "timings" and root.find("timing").get("name") == "A & B",
          "xLights file wraps in <timings> and escapes special characters")

    out = os.path.join(TMP, "_single.lrc")
    th.export_lrc_file(out, [("Vocals", marks)])
    lrc = open(out, encoding="utf-8").read()
    check("[ti:Vocals]" in lrc and "[00:05.00]Chorus" in lrc and lrc.index("Verse 1") < lrc.index("Chorus"),
          "LRC: title header, mm:ss.cc stamps, chronological order")
    out = os.path.join(TMP, "_multi.lrc")
    th.export_lrc_file(out, [("Vocals", marks), ("Drums", [{"start": 1.0, "end": 2.0, "label": "Kick"}])])
    check("[Drums] Kick" in open(out, encoding="utf-8").read(), "multi-track LRC prefixes track names")

    out = os.path.join(TMP, "_aud.txt")
    th.export_audacity_labels_file(out, [("Vocals", marks)])
    fields = [l.split("\t") for l in open(out, encoding="utf-8").read().splitlines() if l]
    check(len(fields) == 3 and all(len(f) == 3 for f in fields), "Audacity: 3 tab-separated fields per mark")
    rng = next(f for f in fields if f[2] == "Chorus")
    check(float(rng[0]) == 5.0 and float(rng[1]) == 10.0, "Audacity range times convert correctly")

    for ext, marker in ((".xtiming", "<timings"), (".lrc", "[ti:"), (".txt", "\t"), (".weird", "<timings")):
        out = os.path.join(TMP, f"_dispatch{ext}")
        th.export_timing_tracks(out, [("Vocals", marks)])
        check(marker in open(out, encoding="utf-8").read(), f"export_timing_tracks picks the format for {ext}")


def test_split_merge_planning(th):
    print("\n-- split / merge planning (text-proportional timing) --")
    rng = {"id": "a", "type": "range", "start": 10.0, "end": 14.0, "label": "hello there world"}
    plan = th.plan_split(rng, text_index=5)
    check(plan["left"][2] == "hello" and plan["right"][2] == "there world",
          "a text-cursor split divides the text at the cursor")
    wl, wr = th.text_weight("hello"), th.text_weight("there world")
    check(abs(plan["left"][1] - (10.0 + 4.0 * wl / (wl + wr))) < 1e-9,
          "...and divides the time by syllable weight (hello = 2 syllables, there + world = 2)")
    plan = th.plan_split(rng, at_time=11.0)
    check(plan["left"][1] == 11.0 and plan["left"][2] == "hello",
          "a time split cuts at the time and splits the text at the nearest word boundary")
    plan = th.plan_split(rng)
    check(plan["left"][2] == "hello" and plan["right"][2] == "there world",
          "with no cursor, a range splits at the word boundary nearest half its syllables")
    plan = th.plan_split({"id": "b", "type": "range", "start": 1.0, "end": 2.0, "label": ""})
    check(plan["left"][1] == 1.5, "an unlabeled range splits at its time midpoint")
    pt = {"id": "c", "type": "point", "start": 3.0, "end": None, "label": "ab cd"}
    plan = th.plan_split(pt, text_index=2)
    check(plan["left"] == (3.0, None, "ab") and plan["right"] == (3.0, None, "cd"),
          "a point mark splits by text only, both halves keeping its time")
    check(th.plan_split(pt) is None, "a point mark can't be split without a text cursor")
    check(th.plan_split(rng, text_index=0) is not None and th.plan_split(rng, text_index=0)["left"][2] != "",
          "a text cursor at the very start falls back to a middle split")
    tiny = {"id": "d", "type": "range", "start": 1.0, "end": 1.015, "label": "a b"}
    check(th.plan_split(tiny) is None, "a split that would make a range shorter than MIN_RANGE is refused")

    marks = [{"id": "1", "start": 1.0, "end": 2.0, "label": "a", "track_id": "t"},
             {"id": "2", "start": 3.0, "end": None, "label": "b", "track_id": "t"},
             {"id": "3", "start": 2.5, "end": 2.7, "label": "x", "track_id": None}]
    check(th.neighbor_mark(marks, marks[0], 1)["id"] == "2", "neighbor_mark stays within the same track")
    check(th.neighbor_mark(marks, marks[1], 1) is None, "the last mark in a track has no next neighbor")
    check(th.merged_fields(marks[1], marks[0]) == (1.0, 3.0, "a b"),
          "merging spans both marks and joins labels in time order")


def test_model_choice_and_regions(aa):
    print("\n-- Whisper model choice + region partitioning --")
    check([aa.default_whisper_model(g) for g in (1, 3, 5, 8, 16)] == ["tiny", "base", "small", "medium", "large-v3"],
          "the auto model scales with free RAM")
    import numpy as np
    sr = 1000
    t = np.arange(10 * sr) / sr
    voc = np.where((t > 2) & (t < 6), np.sin(t * 50), 0).astype(np.float32)
    nov = np.where((t > 4) & (t < 8), np.sin(t * 30), 0).astype(np.float32)
    regions = aa.partition_regions(voc, nov, 10.0, 100)
    kinds = [(round(r["start"], 2), round(r["end"], 2), r["kind"]) for r in regions]
    check(kinds == [(0.0, 2.0, "silent"), (2.0, 4.0, "vocal"), (4.0, 6.0, "mixed"),
                    (6.0, 8.0, "novocal"), (8.0, 10.0, "silent")],
          "stem energy partitions into silent / vocal / mixed / instrumental regions")
    check(aa.region_counts(regions) == {"vocal": 1, "novocal": 1, "mixed": 1, "silent": 2}, "region counts")
    check(aa.vocal_spans(regions, 3.0, 7.0) == [(3.0, 6.0)],
          "vocal_spans merges adjacent vocal+mixed regions and clips to the range")
    check(aa.stem_paths("/x/song.mp3")[0].name == "song-vocals.wav"
          and aa.stem_paths("/x/song.mp3")[1].name == "song-non_vocals.wav",
          "stems use the old audio tab's names")


# ---------------------------------------------------------------------------
# Tests: cache file, metadata, decode
# ---------------------------------------------------------------------------

def test_combined_cache(th, media):
    print("\n-- one combined <stem>-tracked.json per media file --")
    import json
    path = fresh_copy(media, "cachetest")
    check(os.path.basename(th.cache_path(path)) == "cachetest-tracked.json",
          "cache is named <stem>-tracked.json (says which app owns it)")
    other = os.path.splitext(path)[0] + ".mp3"
    check(th.cache_path(other) == th.cache_path(path), "song.wav and song.mp3 share one cache file (accepted)")

    # Old sidecars are no longer migrated (the app wasn't in use yet).
    ident = {"source_mtime": os.path.getmtime(path), "source_size": os.path.getsize(path)}
    json.dump({**ident, "duration": 10.0, "peaks": [[0, 1]] * 5}, open(path + "-waveform-cache.json", "w"))
    json.dump({**ident, "marks": [{"id": "old"}]}, open(path + "-marks.json", "w"))
    check(th.load_marks(path) == [] and th.load_waveform_cache(path) is None,
          "old -marks.json / -waveform-cache.json files are ignored (no migration)")
    check(os.path.exists(path + "-marks.json") and os.path.exists(path + "-waveform-cache.json"),
          "...and left untouched")
    check(not hasattr(th, "_migrate_old_sidecars"), "the migration code is gone")
    os.remove(path + "-marks.json"); os.remove(path + "-waveform-cache.json")

    th.save_marks(path, [{"id": "m"}], [{"id": "t"}])
    th.save_regions(path, [{"start": 0, "end": 1, "kind": "vocal"}])
    th.save_genre_mood(path, {"genre": "pop", "mood": "happy"})
    check(th.load_genre_mood(path) == {"genre": "pop", "mood": "happy"}, "genre/mood is cached")
    check(th.load_genre_mood(path + ".nope") is None, "...and there's none for a file without a cache")

    # Size recorded differently but same timestamp: genre/mood stays, the
    # waveform-derived data is recomputed.
    data = json.load(open(th.cache_path(path)))
    data["source_size"] = data["source_size"] + 1
    json.dump(data, open(th.cache_path(path), "w"))
    check(th.load_genre_mood(path) is not None and th.load_regions(path) == [],
          "genre/mood is only reset by a timestamp change (not by size alone)")
    th.save_marks(path, [{"id": "m"}], [{"id": "t"}])     # rewrites the identity
    check(th.load_genre_mood(path) is not None, "...and survives the next cache write too")

    th.save_regions(path, [{"start": 0, "end": 1, "kind": "vocal"}])
    later = time.time() + 5
    os.utime(path, (later, later))  # e.g. the audio was restored from a backup
    check(th.load_marks(path) == [{"id": "m"}], "marks survive a change to the media file")
    check(th.load_waveform_cache(path) is None and th.load_regions(path) == [],
          "waveform peaks and stem regions are dropped when the media file changes")
    check(th.load_genre_mood(path) is None, "genre/mood is reset when the audio file's timestamp changes")
    th.save_waveform_cache(path, 10.0, [(0, 1)])
    th.save_marks(path, [{"id": "n"}], [])
    data = json.load(open(th.cache_path(path)))
    check(data["marks"] == [{"id": "n"}] and data["duration"] == 10.0 and "genre_mood" not in data,
          "separate section writes don't clobber each other (and the stale genre/mood is gone)")


def test_metadata(th, media_dir):
    print("\n-- metadata: TinyTag or the Sequence Editor's built-in ID3/MP4 readers --")
    mp3 = make_media("tagged", 2, fmt="mp3", extra=("-metadata", "title=Test Song", "-metadata", "artist=Me",
                                                    "-id3v2_version", "3"))
    mp4 = make_media("tagged", 2, fmt="mp4", extra=("-metadata", "title=Vid Song", "-c:a", "aac"))
    saved = th.HAS_TINYTAG
    th.HAS_TINYTAG = False
    try:
        m = th.read_metadata(mp3)
        check(m["source"] == "built-in" and m.get("title") == "Test Song" and m.get("artist") == "Me",
              "without tinytag, ID3v2 tags are read by the built-in reader")
        m = th.read_metadata(mp4)
        check(m.get("title") == "Vid Song" and abs(m.get("duration", 0) - 2.0) < 0.1,
              "without tinytag, MP4 title and duration are read by the built-in reader")
        tags = th.extract_mp3_metadata(os.path.join(media_dir, "tone.wav"))
        check("error" not in tags, "the ID3 reader doesn't error on a file with no tags (e.g. WAV)")
    finally:
        th.HAS_TINYTAG = saved
    if th.HAS_TINYTAG:
        check(th.read_metadata(mp3).get("source") == "tinytag", "tinytag is preferred when installed")


def test_load_and_deep_zoom(th, wt, media):
    print("\n-- waveform load, 4000-point overview, deep-zoom re-decode --")
    path = fresh_copy(media, "zoomtest")
    ctl, canvas, text, tab = open_controller(wt, path)
    check(ctl.audio_duration and abs(ctl.audio_duration - 10.0) < 0.1, "duration is detected")
    check(len(ctl.full_peaks) == th.WAVEFORM_CACHE_RESOLUTION, "the full-file overview has 4000 points")
    check(len(ctl.peaks) == ctl._target_buckets() == 800, "the visible waveform has one column per pixel")

    th.save_waveform_cache(path, ctl.audio_duration, ctl.full_peaks[::2])  # an older 2000-point cache
    ctl2, *_ = open_controller(wt, path)
    check(len(ctl2.full_peaks) == th.WAVEFORM_CACHE_RESOLUTION, "a lower-resolution cache is re-decoded")

    decodes = []
    real = th.decode_waveform_peaks
    th.decode_waveform_peaks = lambda *a, **k: decodes.append(a[1:3]) or real(*a, **k)
    try:
        ctl.view_start, ctl.view_end = 2.0, 6.0          # 1600 overview points for 800 px
        ctl._refresh_view_from_cache()
        run_afters()
        check(decodes == [], "moderate zoom is served from the overview (fast path, no decode)")
        ctl.view_start, ctl.view_end = 3.0, 3.5          # 200 overview points for 800 px
        ctl._refresh_view_from_cache()
        check(195 <= len(ctl.peaks) <= 200, "deep zoom shows the coarse overview immediately")
        run_afters()
        check(len(decodes) == 1 and abs(decodes[0][0] - 2.875) < 1e-9 and abs(decodes[0][1] - 1.5) < 1e-9,
              "...then decodes the view plus 1.75 pages ahead (and 0.25 behind) in the background")
        check(len(ctl.peaks) == 800, "...and redraws with one decoded column per pixel")
        decodes.clear()
        ctl.view_start, ctl.view_end = 3.4, 3.9          # scrolled on by most of a page
        ctl._refresh_view_from_cache()
        check(len(ctl.peaks) == 800 and not decodes,
              "scrolling on to the next page uses the already-decoded detail (no delay at the edge)")
        ctl.view_start, ctl.view_end = 3.7, 4.2          # now within half a page of the decoded end
        ctl._refresh_view_from_cache()
        run_afters()
        check(len(decodes) == 1 and abs(decodes[0][0] - (3.7 - 0.125)) < 1e-9,
              "...near the decoded end, the next stretch is prefetched in the background")
        decodes.clear()
        ctl.view_start, ctl.view_end = 4.5, 5.0
        ctl._refresh_view_from_cache()
        time.sleep(0.2)
        check(len(ctl.peaks) == 800 and all(abs(d[0] - (4.5 - 0.125)) < 1e-9 for d in decodes),
              "the prefetched stretch serves the following page at once (any decode is just the next prefetch)")

        decodes.clear()
        ctl.view_start, ctl.view_end = 1.0, 1.2
        ctl._refresh_view_from_cache()
        ctl.view_start, ctl.view_end = 1.0, 1.1
        ctl._refresh_view_from_cache()
        run_afters()
        check(len(decodes) == 1 and abs(decodes[0][0] - 0.975) < 1e-9 and abs(decodes[0][1] - 0.3) < 1e-9,
              "rapid zoom steps only decode for the final view (debounced)")
    finally:
        th.decode_waveform_peaks = real


# ---------------------------------------------------------------------------
# Tests: marks and tracks (ported from the Sequence Editor's tests)
# ---------------------------------------------------------------------------

def test_mark_interactions(th, wt, media):
    print("\n-- timing mark interactions (click, shift+click, drag, resize) --")
    path = fresh_copy(media, "marktest")
    ctl, canvas, *_ = bare_controller(wt, path)
    x_of = lambda t: (t / 100.0) * 800

    ctl._on_waveform_press(Event(x=100, y=30))
    ctl._on_waveform_release(Event(x=100, y=30))
    check(ctl.marks == [] and abs(ctl.cursor_time - 12.5) < 1e-9,
          "a plain click only moves the @cursor (no mark)")
    ctl._on_waveform_double_click(Event(x=100, y=30))
    check(len(ctl.marks) == 1 and ctl.marks[0]["type"] == "point" and ctl.marks[0]["start"] == 12.5,
          "double-clicking empty waveform adds a point mark there")
    check(ctl.tab.dirty and th.load_marks(path) == [],
          "a new mark flags the tab as having unsaved changes (not written yet)")
    check(ctl.tab.save_hook() and th.load_marks(path) == ctl.marks,
          "the tab's save hook (File > Save / auto-save) writes marks to the cache file")

    ctl._on_waveform_press(Event(x=300, y=30, state=0x0001))
    ctl._on_waveform_release(Event(x=300, y=30, state=0x0001))
    check(len(ctl.marks) == 1 and ctl.marks[0]["type"] == "range",
          "new point + shift-click converts it to a single range, not point+range")

    mark = ctl.marks[0]
    start_x, end_x = int(x_of(mark["start"])), int(x_of(mark["end"]))
    mid_x = (start_x + end_x) // 2
    ctl._on_waveform_motion(Event(x=mid_x, y=50))
    check(canvas.cursor == "fleur", "hovering a range's middle shows the 4-way move cursor")
    ctl._on_waveform_motion(Event(x=start_x, y=50))
    check(canvas.cursor == "left_side", "hovering a range's start edge shows the resize cursor")

    orig_start, orig_end = mark["start"], mark["end"]
    ctl._on_waveform_press(Event(x=mid_x, y=50))
    ctl._on_waveform_drag(Event(x=mid_x + 80, y=50, state=0x0001))
    ctl._on_waveform_release(Event(x=mid_x + 80, y=50, state=0x0001))
    check(mark["start"] > orig_start and abs((mark["end"] - mark["start"]) - (orig_end - orig_start)) < 1e-9,
          "dragging a range's middle moves it, keeping its length")
    orig_start, orig_end = mark["start"], mark["end"]
    ctl._on_waveform_press(Event(x=int(x_of(orig_end)), y=50))
    ctl._on_waveform_drag(Event(x=int(x_of(orig_end)) - 40, y=50, state=0x0001))
    ctl._on_waveform_release(Event(x=int(x_of(orig_end)) - 40, y=50, state=0x0001))
    check(mark["end"] < orig_end and mark["start"] == orig_start, "dragging the end edge moves only the end")

    ctl._delete_all_marks()
    ctl.tab.save_hook()
    check(ctl.marks == [] and th.load_marks(path) == [], "Delete All Marks clears everything")


def test_timing_tracks(th, wt, media):
    print("\n-- timing tracks + undo/redo --")
    path = fresh_copy(media, "tracktest")
    ctl, canvas, *_ = bare_controller(wt, path)
    x_of = lambda t: (t / 100.0) * 800
    mark = ctl._add_mark("range", 10.0, 20.0)
    check(mark["track_id"] is None, "a new mark starts unassigned, in the work area")

    wt.simpledialog.askstring = lambda *a, **k: "Vocals"
    mid_x = int((x_of(10.0) + x_of(20.0)) / 2)
    layout = ctl._track_layout()
    blank_y = layout["row_top"] + ctl.STATUS_ROW_HEIGHT // 2   # the status row is the drop target
    ctl._on_waveform_press(Event(x=mid_x, y=50))
    ctl._on_waveform_drag(Event(x=mid_x, y=blank_y))
    ctl._on_waveform_release(Event(x=mid_x, y=blank_y))
    check(len(ctl.tracks) == 1 and ctl.tracks[0]["name"] == "Vocals",
          "dropping a mark below the waveform creates a named track")
    check(ctl.mark_by_id(mark["id"])["track_id"] == ctl.tracks[0]["id"], "the dragged mark joins the new track")
    ctl.tab.save_hook()
    check(th.load_tracks(path) == ctl.tracks, "tracks are saved to the cache file")

    track_b = ctl._new_track("Drums")
    check(track_b["color"] == ctl.TRACK_PALETTE[1], "the second track gets the second palette color")
    ctl.undo_marks()
    check(len(ctl.tracks) == 1, "undo removes the last track")
    ctl.redo_marks()
    check(len(ctl.tracks) == 2, "redo restores it")
    ctl._delete_track(ctl.tracks[0])
    check(all(m.get("track_id") != mark["track_id"] for m in ctl.marks),
          "deleting a track also deletes its marks")
    wt.simpledialog.askstring = lambda *a, **k: None


# ---------------------------------------------------------------------------
# Tests: features added in trackED
# ---------------------------------------------------------------------------

def test_split_merge_controller(th, wt, media):
    print("\n-- split / merge on the waveform (and right-click menu) --")
    path = fresh_copy(media, "splittest")
    ctl, canvas, *_ = bare_controller(wt, path)
    tr = ctl._new_track("Lyrics")
    a = ctl._add_mark("range", 10.0, 20.0, label="one two three four", track_id=tr["id"])
    b = ctl._add_mark("range", 21.0, 22.0, label="five", track_id=tr["id"])
    ctl.cursor_time = 15.0
    check(ctl.split_mark_by_id(a["id"]), "a range splits at the Ctrl+click cursor")
    parts = ctl.track_marks(tr["id"])
    check([(p["start"], p["end"]) for p in parts[:2]] == [(10.0, 15.0), (15.0, 20.0)],
          "the two halves meet at the cursor")
    check(parts[0]["label"] and parts[1]["label"] and " ".join([parts[0]["label"], parts[1]["label"]])
          == "one two three four", "the words are divided between the halves, none lost")
    check(ctl.merge_mark_by_id(parts[0]["id"], 1), "Merge with Next")
    check(ctl.track_marks(tr["id"])[0]["label"] == "one two three four"
          and len(ctl.track_marks(tr["id"])) == 2, "merging restores one range with the joined text")
    ctl.undo_marks()
    check(len(ctl.track_marks(tr["id"])) == 3, "merge can be undone")

    captured = []
    orig = wt.tk.Menu

    class Capture(orig):
        def __init__(self, *args, **kw):
            super().__init__(*args, **kw)
            captured.append(self)

    wt.tk.Menu = Capture
    try:
        ctl.cursor_time = 21.5
        layout = ctl._track_layout()
        ctl._on_waveform_right_click(Event(x=int(21.3 / 100 * 800), y=layout["track_top"] + 5))
    finally:
        wt.tk.Menu = orig
    menu = next(m for m in captured if "Split at Cursor" in m.labels())
    check(ctl.selected == ("mark", b["id"]), "right-clicking a mark in a track band selects it")
    check(menu.labels()[:4] == ["Split at Cursor", "Merge with Previous", "Merge with Next", "Transcribe Range"],
          "the mark menu offers split / merge / transcribe")
    check(menu.entry("Merge with Next").get("state") == "disabled", "no next neighbor -> Merge with Next disabled")


def test_timing_panel(th, wt, media):
    print("\n-- timing panel in the text area --")
    path = fresh_copy(media, "paneltest")
    ctl, canvas, text, tab = bare_controller(wt, path)
    ctl.set_info_text("INFO TEXT\n")
    tr = ctl._new_track("Lyrics")
    m1 = ctl._add_mark("range", 2.0, 6.0, label="hello there world", track_id=tr["id"])
    m2 = ctl._add_mark("point", 8.0, None, label="hey", track_id=tr["id"])
    loose = ctl._add_mark("point", 50.0, None)
    panel = ctl.panel

    ctl.selected = ("track", tr["id"]); ctl.render_waveform()
    check(panel.mode == "track" and list(panel.cards) == [m1["id"], m2["id"]],
          "selecting a track shows one card per mark, in time order")
    card = panel.cards[m1["id"]]
    check((card["start"].get(), card["end"].get(), card["text"].get()) == ("0:02.000", "0:06.000", "hello there world"),
          "a card shows start, end and text")
    check(panel.cards[m2["id"]]["end"].get() == "", "a point mark's End is blank")
    ctl.selected = ("mark", loose["id"]); ctl.render_waveform()
    check(panel.mode == "info" and "INFO TEXT" in text.get(), "selecting a mark outside any track restores the info text")
    ctl.selected = ("mark", m2["id"]); ctl.render_waveform()
    check(panel.mode == "track", "selecting a mark inside a track shows that track")

    card = panel.cards[m1["id"]]
    card["start"].type_text("2.5"); card["start"].fire("<Return>")
    check(ctl.mark_by_id(m1["id"])["start"] == 2.5, "typing a start time + Enter applies it")
    card["end"].type_text("2:00"); card["end"].fire("<Return>")
    check(abs(ctl.mark_by_id(m1["id"])["end"] - 110.0) < 1e-9,
          "an End typed past the audio's end is limited to 10% past it")
    card["end"].type_text("6"); card["end"].fire("<Return>")
    card["end"].type_text("junk"); card["end"].fire("<FocusOut>")
    check(ctl.mark_by_id(m1["id"])["end"] == 6.0, "an unparseable time is rejected")
    card["text"].type_text("hello there world again"); card["text"].fire("<FocusOut>")
    check(ctl.mark_by_id(m1["id"])["label"] == "hello there world again", "editing the text updates the label")

    panel.step_var.set("0.25")
    panel._nudge(m1["id"], "end", -1)
    check(ctl.mark_by_id(m1["id"])["end"] == 5.75, "the - button nudges by the Step")
    ctl.cursor_time = 3.0
    panel._to_cursor(m1["id"], "start")
    check(ctl.mark_by_id(m1["id"])["start"] == 3.0, "@ sets a time to the cursor/playback position")
    card = panel.cards[m2["id"]]
    card["end"].type_text("9"); card["end"].fire("<Return>")
    check(ctl.mark_by_id(m2["id"])["type"] == "range", "giving a point an End turns it into a range")
    card = panel.cards[m2["id"]]
    card["end"].type_text(""); card["end"].fire("<Return>")
    check(ctl.mark_by_id(m2["id"])["type"] == "point", "clearing End turns a range back into a point")

    card = panel.cards[m1["id"]]
    card["text"].icursor(len("hello"))
    panel._split(m1["id"])
    first, second = ctl.track_marks(tr["id"])[:2]
    check((first["label"], second["label"]) == ("hello", "there world again"),
          "Split uses the text cursor position in the card")
    weight_left, weight_right = th.text_weight("hello"), th.text_weight("there world again")
    expect = 3.0 + (5.75 - 3.0) * weight_left / (weight_left + weight_right)
    check(abs(first["end"] - expect) < 1e-9 and second["start"] == first["end"],
          "...and divides the range's time in proportion to the text")
    check(len(panel.cards) == 3, "the panel rebuilds with the new card")
    panel._merge_next(first["id"])
    check(ctl.track_marks(tr["id"])[0]["label"] == "hello there world again", "Merge v joins with the next card")

    card = panel.cards[ctl.track_marks(tr["id"])[0]["id"]]
    FOCUS["w"] = card["text"]
    card["text"].type_text("typing in progress")
    ctl.render_waveform()
    check(card["text"].get() == "typing in progress", "redraws never overwrite a field being edited")
    FOCUS["w"] = None
    check(getattr(tab, "protect_file", False), "the audio tab is protected from File > Save")


def test_playback_loop_and_cursor(th, wt, media):
    print("\n-- Shift+Play loop, Ctrl+click cursor --")
    path = fresh_copy(media, "looptest")
    ctl, canvas, *_ = bare_controller(wt, path)
    rng = ctl._add_mark("range", 3.0, 5.0)
    ctl.selected = ("mark", rng["id"])
    ctl._on_play_btn_release(Event(state=0x0001))
    ctl.toggle_play()
    check(ctl._loop and (ctl._play_seg_start, ctl._play_seg_end) == (3.0, 5.0), "Shift+Play loops the selected range")
    check("Loop" in ctl.play_status_var.get(), "the status shows Looping")
    ctl.engine.active = False
    ctl._poll_playback()
    check(ctl.engine.calls == [(3.0, 2.0), (3.0, 2.0)], "when the range ends, playback restarts at its start")
    ctl.stop_play()
    check(not ctl._loop and ctl._play_state == "stopped", "Stop ends the loop")

    pt = ctl._add_mark("point", 90.0, None)
    ctl.selected = ("mark", pt["id"])
    ctl._on_play_btn_release(Event(state=0x0001)); ctl.toggle_play()
    check((ctl._play_seg_start, ctl._play_seg_end) == (90.0, None), "Shift+Play on a point loops to the end of the audio")
    ctl.stop_play()

    ctl._set_play_cursor(True)
    check(ctl.play_btn.cget("cursor") == "exchange", "Shift over Play shows the loop cursor")
    ctl._set_play_cursor(False)
    check(ctl.play_btn.cget("cursor") == "hand2", "without Shift the Play button keeps its hand cursor")

    ctl.selected = None
    ctl._on_ctrl_press(Event(x=400, y=30, state=0x0004))
    check(abs(ctl.cursor_time - 50.0) < 1e-9 and ctl.marks[-1]["id"] == pt["id"],
          "Ctrl+click places the @cursor without creating a mark")


def test_cursor_playhead_model(th, wt, media):
    print("\n-- one @cursor = the playhead: Play / Pause / Reset / skip --")
    path = fresh_copy(media, "cursormodel")
    ctl, canvas, *_ = bare_controller(wt, path)
    rng = ctl._add_mark("range", 60.0, 70.0)
    ctl.selected = ("mark", rng["id"])          # a selection no longer decides where Play starts
    ctl.cursor_time = 20.0
    ctl.render_waveform()
    lines = [it for it in canvas.items if "cursor_line" in (it.get("tags") or ())]
    at = [it for it in canvas.items if "cursor_at" in (it.get("tags") or ())]
    check(lines and at, "the @cursor is always shown (line + '@' tag), even when stopped")
    check(not [it for it in canvas.items if it.get("fill") == "#ff2222"],
          "there is no separate red playhead line any more (it looked like an extra point mark)")
    ctl.skip_play(5.0)
    check(abs(ctl.cursor_time - 25.0) < 1e-9, "skip forward moves the @cursor while stopped")
    ctl.skip_play(-5.0); ctl.skip_play(-5.0)
    check(abs(ctl.cursor_time - 15.0) < 1e-9, "skip back moves it too")
    time.sleep(ctl.SEEK_CLICK_WINDOW + 0.05)

    ctl.toggle_play()
    check(ctl._play_state == "playing" and ctl.engine.calls[-1] == (15.0, None),
          "Play starts from the @cursor and plays to the end of the audio")
    time.sleep(0.2)
    ctl._poll_playback()
    check(ctl.cursor_time > 15.0, "while playing, the @cursor moves with playback")
    lines = [it for it in canvas.items if "cursor_line" in (it.get("tags") or ())]
    check(lines and lines[0].get("width") == 2 and not lines[0].get("dash"), "...drawn solid while playing")
    ctl.toggle_play()
    paused_at = ctl.cursor_time
    check(ctl._play_state == "paused" and paused_at > 15.0, "Pause freezes the @cursor where it is")
    time.sleep(0.1)
    check(ctl.cursor_position() == paused_at, "...and it stays there while paused")
    ctl.skip_play(5.0)
    check(abs(ctl.cursor_time - (paused_at + 5.0)) < 1e-9 and ctl._play_state == "paused",
          "skip while paused moves the @cursor, still paused")
    time.sleep(ctl.SEEK_CLICK_WINDOW + 0.05)
    ctl.toggle_play()
    check(ctl.engine.calls[-1][0] == round(paused_at + 5.0, 3), "Play resumes from the (moved) @cursor")
    ctl.toggle_play()
    ctl.stop_play()
    check(ctl._play_state == "stopped" and abs(ctl.cursor_time - 15.0) < 1e-9,
          "Reset puts the @cursor back where Play was first pressed")
    ctl.toggle_play()
    check(ctl.engine.calls[-1] == (15.0, None), "pause -> Reset -> Play restarts from the starting position")
    ctl.toggle_play(); ctl.stop_play()
    check(ctl.play_stop_btn.cget("text") == "\u25a0", "the Reset button keeps its square glyph")

    ctl.engine.calls.clear()
    ctl.cursor_time = 98.0
    ctl.toggle_play()
    ctl.engine.active = False             # reached the end on its own
    ctl._poll_playback()
    check(ctl._play_state == "stopped" and ctl.cursor_time == 98.0,
          "when playback ends by itself, the @cursor returns to where Play started")

    # speed / volume changes restart at the current spot, not the start
    ctl.cursor_time = 30.0
    ctl.toggle_play(); time.sleep(0.15)
    ctl.change_volume(-0.1)
    check(ctl.engine.calls[-1][0] > 30.0, "changing volume mid-playback continues from the current spot")
    ctl.change_volume(0.1)
    ctl.stop_play()


def test_shift_click_anchor(th, wt, media):
    print("\n-- Shift+click on the waveform --")
    path = fresh_copy(media, "shiftclick")
    ctl, canvas, *_ = bare_controller(wt, path)
    ctl.cursor_time = 10.0
    ctl._on_waveform_press(Event(x=240, y=30, state=0x0001))          # 30 s, with Shift, no previous click
    ctl._on_waveform_release(Event(x=240, y=30, state=0x0001))
    m = ctl.marks[-1]
    check(len(ctl.marks) == 1 and m["type"] == "range" and (m["start"], m["end"]) == (10.0, 30.0),
          "Shift+click with no previous click makes a range from the @cursor")
    ctl._on_waveform_press(Event(x=400, y=30)); ctl._on_waveform_release(Event(x=400, y=30))   # plain click at 50 s
    ctl._on_waveform_press(Event(x=480, y=30, state=0x0001)); ctl._on_waveform_release(Event(x=480, y=30, state=0x0001))
    m = ctl.marks[-1]
    check(len(ctl.marks) == 2 and (m["start"], m["end"]) == (50.0, 60.0),
          "Shift+click right after a click extends that click's point into a range")
    ctl._on_waveform_press(Event(x=640, y=30, state=0x0001)); ctl._on_waveform_release(Event(x=640, y=30, state=0x0001))
    m = ctl.marks[-1]
    check(len(ctl.marks) == 3 and (m["start"], m["end"]) == (50.0, 80.0),
          "a second Shift+click anchors at the @cursor again (where the last click put it), not at an old mark")
    ctl.cursor_time = 5.0
    ctl.canvas.fire("<Key-m>", Event())
    check(ctl.marks[-1]["type"] == "point" and ctl.marks[-1]["start"] == 5.0, "M adds a point mark at the @cursor")


def test_stem_tracks(th, wt, media):
    print("\n-- timing tracks from stems (Stems \u25be menu) --")
    path = fresh_copy(media, "stemtracks")
    ctl, canvas, *_ = bare_controller(wt, path)
    ctl._fill_stems_menu()
    check(any("run Stems first" in e["label"] for e in ctl.stems_menu.entries), "before stems: the menu says so")
    ctl._set_regions([{"start": 0.0, "end": 10.0, "kind": "novocal"}, {"start": 10.0, "end": 20.0, "kind": "vocal"},
                      {"start": 20.0, "end": 30.0, "kind": "novocal"}, {"start": 30.0, "end": 100.0, "kind": "vocal"}])
    ctl.stems_menu.entries.clear()
    ctl._fill_stems_menu()
    labels = [e["label"] for e in ctl.stems_menu.entries]
    check(any("Vocals (2 regions)" in l for l in labels) and any("Instrumental (2 regions)" in l for l in labels)
          and not any(("Mixed (" in l and " or " not in l) or "Silence" in l for l in labels),
          "the menu lists only the non-empty stems, with region counts")
    entry = next(e for e in ctl.stems_menu.entries if "All non-empty" in e["label"])
    entry["command"]()
    check([t["name"] for t in ctl.tracks] == ["Vocals", "Instrumental"], "'All non-empty stems' makes one track per stem")
    voc = ctl.tracks[0]
    marks = ctl.track_marks(voc["id"])
    check([(m["start"], m["end"]) for m in marks] == [(10.0, 20.0), (30.0, 100.0)] and all(m["type"] == "range" for m in marks),
          "each region becomes a range mark in its stem's track")
    check(voc["color"] == wt.REGION_COLORS["vocal"], "stem tracks use the stem's region color")
    check(ctl.tab.dirty, "the new tracks are unsaved changes like any other edit")
    ctl.undo_marks()
    check(ctl.tracks == [], "creating stem tracks is a single undo step")
    one = next(e for e in ctl.stems_menu.entries if "Vocals (2" in e["label"])
    one["command"]()
    check([t["name"] for t in ctl.tracks] == ["Vocals"], "a single stem can be turned into a track too")


def test_dial_geometry_sash():
    print("\n-- auto-save dial, window size, sash persistence --")
    import editor_tab
    import tracked
    import utils
    frames = []
    orig = editor_tab.tk.PhotoImage

    class Img(FakeWidget):
        def __init__(self, *a, **k):
            super().__init__(*a, **k)
            self.pixels = {}
            frames.append(self)
        def put(self, color, xy):
            self.pixels[xy] = color
    editor_tab.tk.PhotoImage = Img
    editor_tab._dial_imgs.clear()
    try:
        master = FakeWidget()
        d0 = editor_tab._autosave_dial(master, 0.0)
        dhalf = editor_tab._autosave_dial(master, 0.5)
        dfull = editor_tab._autosave_dial(master, 1.0)
    finally:
        editor_tab.tk.PhotoImage = orig
    red = lambda img: sum(1 for c in img.pixels.values() if c == editor_tab.DIRTY_MARKER_COLOR)
    check(len(frames) == editor_tab.DIAL_FRAMES + 1, "the dial's frames are drawn once")
    check(red(d0) < red(dhalf) < red(dfull), "the red wedge grows as auto-save approaches")
    check(dhalf.pixels.get((7, 3)) == editor_tab.DIRTY_MARKER_COLOR and dhalf.pixels.get((3, 7)) != editor_tab.DIRTY_MARKER_COLOR,
          "it fills clockwise from 12 o'clock (right half first)")

    calls = []
    notebook = FakeWidget()
    notebook.tab = lambda frame, **kw: calls.append(kw)
    fake = types.SimpleNamespace(notebook=notebook, frame=FakeWidget(), filepath=os.path.join(TMP, "song.mp3"),
                                 dirty=True, dirty_since=time.monotonic() - 5)
    fake._label_text = lambda: editor_tab.EditorTab._label_text(fake)
    fake._autosave_fraction = lambda: editor_tab.EditorTab._autosave_fraction(fake)
    editor_tab._dial_imgs.clear()
    editor_tab.tk.PhotoImage = Img
    try:
        editor_tab.EditorTab.update_tab_label(fake)
    finally:
        editor_tab.tk.PhotoImage = orig
    frames_now = editor_tab._dial_imgs[list(editor_tab._dial_imgs)[0]]
    check(calls[-1]["image"] is frames_now[editor_tab.DIAL_FRAMES // 2],
          "an unsaved tab 5 s into a 10 s auto-save shows the half-full dial")

    # window size
    app = types.SimpleNamespace(geometry=lambda g=None: app.__dict__.setdefault("geo", []).append(g) or "1200x800+50+40",
                                winfo_screenwidth=lambda: 1920, winfo_screenheight=lambda: 1080,
                                state=lambda s=None: "normal", attributes=lambda *a: False)
    tracked.EditorApp._save_window_geometry(app)
    check(utils.get_preference("window_geometry") == "1200x800+50+40" and not utils.get_preference("window_maximized"),
          "the window size/position is saved on quit")
    app.geo = []
    utils.set_preference("window_geometry", "5000x4000+9000+9000")
    tracked.EditorApp._restore_window_geometry(app)
    check(app.geo[-1] == "1920x1080+1820+980", "a saved size bigger than the screen is kept on screen")
    utils.set_preference("window_geometry", "1200x800+50+40")
    tracked.EditorApp._restore_window_geometry(app)
    check(app.geo[-1] == "1200x800+50+40", "the saved size/position is restored on start")

    # sash: not applied (or saved) before the pane has its real size
    calls = []

    class Paned(FakeWidget):
        height, mapped, pos = 1, False, 123
        def sashpos(self, i, pos=None):
            if pos is None:
                return self.pos
            calls.append(pos)
        def winfo_height(self): return self.height
        def winfo_ismapped(self): return self.mapped
    paned = Paned()
    fake = types.SimpleNamespace(filepath=os.path.join(TMP, "sashy.wav"), paned=paned, frame=FakeWidget(),
                                 min_sash=None, preferred_sash=200, _sash_ready=False)
    fake._sash_hint = lambda name: editor_tab.EditorTab._sash_hint(fake, name)
    fake._restore_sash = lambda attempt=0: editor_tab.EditorTab._restore_sash(fake, attempt)
    utils.set_sash_pos(fake.filepath, 300)
    AFTERS.clear()
    editor_tab.EditorTab._restore_sash(fake)
    check(calls == [] and not fake._sash_ready, "a pane that isn't laid out yet isn't given the sash (it would be lost)")
    editor_tab.EditorTab._on_sash_released(fake)
    check(utils.get_sash_pos(fake.filepath) == 300, "...and a hidden tab never overwrites the saved sash")
    run_afters(sleep=0)
    check(paned._binds.get("<Map>"), "after retrying briefly, it waits for the tab to be shown")
    paned.height, paned.mapped = 700, True
    paned.fire("<Map>")
    check(calls == [300] and fake._sash_ready, "when shown, the saved sash is applied")
    paned.pos = 333
    editor_tab.EditorTab._on_sash_released(fake)
    check(utils.get_sash_pos(fake.filepath) == 333, "and a real drag is saved")



def test_toolbar_layout(th, wt, media):
    print("\n-- toolbar row; status / drop row under the waveform; tracks below it --")
    path = fresh_copy(media, "layouttest")
    ctl, canvas, text, tab = bare_controller(wt, path)
    check(len(ctl._toolbars) == 1, "a single toolbar row above the waveform (status moved into the canvas)")
    layout = ctl._track_layout()
    check(layout["row_top"] == layout["work_height"]
          and layout["track_top"] == layout["row_top"] + ctl.STATUS_ROW_HEIGHT,
          "the status / drop row sits right under the waveform")
    tr = ctl._new_track("Lyrics")
    layout = ctl._track_layout()
    check(ctl._track_zone_at_y(layout["row_top"] + 3) == ("new_track", None),
          "the status row is the new-track drop target")
    check(ctl._track_zone_at_y(layout["track_top"] + 3) == ("track", tr["id"]),
          "named tracks are below the status row")
    check(layout["track_top"] + ctl.TRACK_HEIGHT == layout["total_h"],
          "no extra empty drop row at the bottom any more")

    ctl.cursor_time = 83.456
    ctl.render_waveform()
    check(ctl.time_var.get() == " 1:23.456 / 1:40.000", "the readout shows @cursor / total, fixed width")
    check(ctl.view_var.get() == "0:00.000 \u2013 1:40.000", "the toolbar shows the visible range")
    status = [it for it in canvas.items if "status_text" in (it.get("tags") or ())]
    check(not status or "0:00.000" not in status[0]["text"], "...no longer in the status row")
    h = ctl._canvas_size()[1]
    corner = [it for it in canvas.items if it["kind"] == "text" and it["coords"][1] == h - 4]
    check(not corner, "the start/end times in the waveform's lower corners are gone")
    at = [it for it in canvas.items if it["kind"] == "text" and "cursor_at" in (it.get("tags") or ())]
    check(at and at[0]["text"] == "@" and layout["row_top"] < at[0]["coords"][1] < layout["track_top"],
          "the @cursor line has an '@' where it crosses the status row")
    ctl.analysis_status_var.set("Stems ready")
    run_afters()
    status = [it for it in canvas.items if "status_text" in (it.get("tags") or ())]
    check("Stems ready" in status[0]["text"], "a status change redraws the row")
    check(not [it for it in canvas.items if "legend" in (it.get("tags") or ())],
          "no region color key before stems exist")
    ctl._set_regions([{"start": 0, "end": 1, "kind": "vocal"}])
    run_afters()
    check(len([it for it in canvas.items if "legend" in (it.get("tags") or ())]) == 8,
          "the color key (4 chips + names) appears in the row once regions exist")
    check(not [it for it in canvas.items if "drop_hint" in (it.get("tags") or ())],
          "with tracks and no drag in progress, the drop hint stays hidden")

    ctl.play_speed_var.set("2x"); ctl._on_play_speed_changed()
    check(ctl.speed_btn.cget("text") == "2x \u25be" and ctl._play_speed_value() == 2.0,
          "the speed menu updates its button and the playback speed")
    check(ctl.play_btn.cget("bg") == wt.TB_BTN and ctl.play_btn.cget("fg") == wt.TB_FG,
          "toolbar buttons use the dark palette; Play is colored like the others (no accent)")
    ctl.play_btn.fire("<Enter>", Event())
    check(ctl.play_btn.cget("bg") == wt.TB_HOVER, "toolbar buttons highlight on hover")
    ctl.play_btn.fire("<Leave>", Event())
    saved = dict(th.OPTIONAL_MISSING)
    th.OPTIONAL_MISSING.clear(); th.OPTIONAL_MISSING["tinytag"] = "tinytag"
    ctl._refresh_playback_availability()
    shown = ctl.install_btn.packed and "tinytag" in ctl._install_tip.text
    th.OPTIONAL_MISSING.clear()
    ctl._refresh_playback_availability()
    hidden = not ctl.install_btn.packed
    th.OPTIONAL_MISSING.update(saved)
    check(shown and hidden, "the warning button only appears when packages are missing, naming them")
    ctl.model_var.set("medium"); ctl._on_model_changed()
    check(ctl._selected_model() == "medium", "choosing a model in the Transcribe menu selects it")


def test_cards_delete_repeat_colors(th, wt, media):
    print("\n-- timing cards: delete, hold-to-repeat -/+, track colors --")
    import timing_panel as tp
    path = fresh_copy(media, "cardtest")
    ctl, canvas, text, tab = bare_controller(wt, path)
    tr = ctl._new_track("Lyrics")
    m1 = ctl._add_mark("range", 2.0, 3.0, label="a", track_id=tr["id"])
    m2 = ctl._add_mark("range", 5.0, 6.0, label="b", track_id=tr["id"])
    ctl.selected = ("track", tr["id"]); ctl.render_waveform()
    card = ctl.panel.cards[m1["id"]]
    mark_color = th.blend_color(tr["color"], 0.25, tp.CARD_DARK_BASE)
    check(card["frame"].cget("bg") == mark_color, "a card's background is a dark shade of its track's color")
    check(card["num"].cget("fg") == tp.contrast_fg(mark_color), "card label text contrasts with that color")
    ctl.selected = ("mark", m1["id"]); ctl.render_waveform()
    check(ctl.panel.cards[m1["id"]]["frame"].cget("bg") == th.blend_color(ctl.SELECTION_COLOR, 0.45, tp.CARD_DARK_BASE),
          "the selected card uses a dark shade of the waveform's selection color")
    check(tp.contrast_fg("#ffe066") == tp.DARK_TEXT and tp.contrast_fg("#202040") == tp.LIGHT_TEXT,
          "dark text on light colors, light text on dark ones")

    card = ctl.panel.cards[m1["id"]]
    nudgers = [b for b in card["frame"].winfo_children() if b._cfg.get("text") in ("\u2212", "+")]
    check(len(nudgers) == 4 and all(b.cget("repeatdelay") == 1000 and b.cget("repeatinterval") > 0
                                    for b in nudgers),
          "the -/+ buttons auto-repeat after being held for 1 second")
    ctl.panel.step_var.set("0.25")
    for _ in range(10):           # like holding "-" on Start
        ctl.panel._nudge(m1["id"], "start", -1)
    check(ctl.mark_by_id(m1["id"])["start"] == 0.0, "holding - on Start stops at 0")
    for _ in range(40):           # like holding "+" on Start
        ctl.panel._nudge(m1["id"], "start", 1)
    check(abs(ctl.mark_by_id(m1["id"])["start"] - (3.0 - th.MIN_RANGE)) < 1e-9,
          "holding + on Start stops just short of End")
    for _ in range(40):
        ctl.panel._nudge(m1["id"], "end", -1)
    m = ctl.mark_by_id(m1["id"])
    check(abs(m["end"] - (m["start"] + th.MIN_RANGE)) < 1e-9, "holding - on End stops just after Start")
    for _ in range(1000):
        ctl.panel._nudge(m2["id"], "end", 1)
    check(abs(ctl.mark_by_id(m2["id"])["end"] - 110.0) < 1e-9, "holding + on End stops 10% past the end of the audio")

    card = ctl.panel.cards[m2["id"]]
    check(card["delete"].cget("text") == "\u2715", "each card has a delete button in its header row")
    card["delete"]._cfg["command"]()
    check(ctl.mark_by_id(m2["id"]) is None and len(ctl.panel.cards) == 1, "the delete button removes the mark")
    ctl.undo_marks()
    check(ctl.mark_by_id(m2["id"]) is not None, "...and it can be undone")


def test_card_editor_extras(th, wt, media):
    print("\n-- card editor: select-all, snap to neighbors, Play/Pause + Shift loop, click-off --")
    path = fresh_copy(media, "cardextras")
    ctl, canvas, text, tab = bare_controller(wt, path)
    tr = ctl._new_track("Lyrics")
    a = ctl._add_mark("range", 2.0, 3.0, label="a", track_id=tr["id"])
    b = ctl._add_mark("range", 5.0, 6.0, label="b", track_id=tr["id"])
    c = ctl._add_mark("point", 8.0, None, label="c", track_id=tr["id"])
    ctl.selected = ("mark", b["id"]); ctl.render_waveform()
    panel = ctl.panel

    card = panel.cards[b["id"]]
    for key in ("start", "end", "text"):
        card[key].fire("<FocusIn>")
    run_afters()
    check(all(card[k].selection == (0, "end") for k in ("start", "end"))
          and card["text"].selected_span() == (0, len(card["text"].get())),
          "clicking into Start, End or the text selects the whole current value")

    card["start_snap"]._cfg["command"]()
    check(ctl.mark_by_id(b["id"])["start"] == 3.0, "\u21e4 sets Start to the end of the previous mark")
    card = panel.cards[b["id"]]
    card["end_snap"]._cfg["command"]()
    check(ctl.mark_by_id(b["id"])["end"] == 8.0, "\u21e5 sets End to the start of the next mark (a point here)")
    panel.cards[a["id"]]["start_snap"]._cfg["command"]()
    check(ctl.mark_by_id(a["id"])["start"] == 0.0, "the first card's \u21e4 snaps Start to 0:00")
    ctl.set_mark_times(c["id"], 8.0, 9.0)     # make the last one a range
    panel.cards[c["id"]]["end_snap"]._cfg["command"]()
    check(ctl.mark_by_id(c["id"])["end"] == 100.0, "the last card's \u21e5 snaps End to the end of the audio")
    card = panel.cards[a["id"]]
    card["end_snap"]._cfg["command"]()
    check(ctl.mark_by_id(a["id"])["end"] == 3.0, "snapping End onto a neighbor that already touches is harmless")

    card = panel.cards[b["id"]]
    card["play"]._cfg["command"]()
    check(ctl._play_state == "playing" and ctl._play_mark_id == b["id"], "a card's Play button plays its mark")
    check(panel.cards[b["id"]]["play"].cget("text") == "\u275a\u275a", "...and turns into a Pause button")
    check(panel.cards[a["id"]]["play"].cget("text") == "\u25b6", "other cards keep their Play glyph")
    panel.cards[b["id"]]["play"]._cfg["command"]()
    check(ctl._play_state == "paused" and panel.cards[b["id"]]["play"].cget("text") == "\u25b6",
          "clicking it again pauses (and it shows Play)")
    panel.cards[b["id"]]["play"]._cfg["command"]()
    check(ctl._play_state == "playing", "...and again resumes")
    ctl.stop_play()
    btn = panel.cards[a["id"]]["play"]
    btn.fire("<ButtonRelease-1>", Event(state=0x0001))
    btn._cfg["command"]()
    am = ctl.mark_by_id(a["id"])
    check(ctl._loop and (ctl._play_seg_start, ctl._play_seg_end) == (am["start"], am["end"]),
          "Shift+click on a card's Play loops that card's span")
    btn.fire("<Motion>", Event(state=0x0001))
    check(btn.cget("cursor") == "exchange", "Shift over a card's Play shows the loop cursor")
    ctl.stop_play()

    ctl.selected = ("mark", b["id"]); ctl.render_waveform()
    ev = Event(); ev.widget = text
    card = panel.cards[b["id"]]
    FOCUS["w"] = card["text"]
    card["text"].type_text("typed then clicked away")
    ctl._move_drag = {"mark": b}
    text.fire("<Button-1>", ev)
    check(ctl.selected == ("mark", b["id"]), "clicking off is ignored while the mouse is busy with a drag")
    ctl._move_drag = None
    # focus_set on the Text moves focus; the card field's FocusOut then commits
    orig_focus = FakeText.focus_set
    def focus_and_blur(self_):
        prev = FOCUS["w"]
        FOCUS["w"] = self_
        if prev is not None and prev is not self_:
            prev.fire("<FocusOut>")
    orig_cfocus = FakeCanvas.focus_set
    FakeText.focus_set = focus_and_blur
    FakeCanvas.focus_set = focus_and_blur
    try:
        result = text.fire("<Button-1>", ev)
    finally:
        FakeText.focus_set = orig_focus
        FakeCanvas.focus_set = orig_cfocus
    check(ctl.selected == ("track", tr["id"]) and panel.mode == "track",
          "clicking off the cards deselects the card but keeps the track's panel")
    check(ctl.mark_by_id(b["id"])["label"] == "typed then clicked away", "...committing what was typed")
    check(result == "break", "...without the click doing anything else in the panel")


def test_tab_dirty_marker():
    print("\n-- unsaved-changes marker on the tab --")
    import editor_tab
    calls = []
    notebook = FakeWidget()
    notebook.tab = lambda frame, **kw: calls.append(kw)
    fake = types.SimpleNamespace(notebook=notebook, frame=FakeWidget(), filepath=os.path.join(TMP, "song.mp3"),
                                 dirty=True)
    fake._label_text = lambda: editor_tab.EditorTab._label_text(fake)
    fake._autosave_fraction = lambda: None   # auto-save off: the plain red asterisk
    editor_tab.EditorTab.update_tab_label(fake)
    check(calls[-1].get("image") is not None and calls[-1]["image"] != "" and calls[-1]["text"] == "song.mp3"
          and calls[-1].get("compound") == "left",
          "an unsaved tab shows a red asterisk image before its name")
    fake.dirty = False
    editor_tab.EditorTab.update_tab_label(fake)
    check(calls[-1].get("image") == "" and calls[-1]["text"] == "song.mp3", "a saved tab shows just its name")
    check(editor_tab.DIRTY_MARKER_COLOR.lower() in ("#d0021b",), "the marker is red")


def test_round5(th, wt, media):
    print("\n-- card layout/stop, region snaps, @ while paused, seek clicks, volume, zoom past end --")
    import utils
    path = fresh_copy(media, "round5")
    ctl, canvas, text, tab = bare_controller(wt, path)
    tr = ctl._new_track("Lyrics")
    a = ctl._add_mark("range", 12.0, 18.0, label="a", track_id=tr["id"])
    ctl.selected = ("mark", a["id"]); ctl.render_waveform()
    panel = ctl.panel
    card = panel.cards[a["id"]]
    kids = card["frame"].winfo_children()
    order = [k._cfg.get("text") for k in kids]
    check(kids.index(card["play"]) < kids.index(card["start"]) and kids.index(card["stop"]) < kids.index(card["start"]),
          "a card's Play (and Stop) sit left of the Start/End times")
    right = [kids.index(card["split"]), kids.index(card["merge"]), kids.index(card["delete"])]
    check(min(right) > kids.index(card["end_rsnap"]), "Split / Merge / Delete stay on the right")
    check(getattr(card["play"], "_loop_hover", False), "card Play buttons are marked for the Shift-key loop cursor")

    # Stop buttons only while paused
    check(not ctl.play_stop_btn.packed, "the main Stop button is hidden while stopped")
    card["play"]._cfg["command"]()
    check(not ctl.play_stop_btn.packed and not getattr(card["stop"], "_gridded", False),
          "...and while playing")
    card["play"]._cfg["command"]()      # pause
    check(ctl.play_stop_btn.packed, "the main Stop button appears while paused")
    check(getattr(card["stop"], "_gridded", False), "the paused card shows its Stop button")
    at = [it for it in canvas.items if it["kind"] == "text" and "cursor_at" in (it.get("tags") or ())]
    check(at and abs(at[0]["coords"][0] - ctl._play_position / 100 * 800) < 1.0,
          "while paused, the '@' tag sits at the playhead")
    card["stop"]._cfg["command"]()
    check(ctl._play_state == "stopped" and not ctl.play_stop_btn.packed and not card["stop"]._gridded,
          "a card's Stop resets playback and the Stop buttons hide again")

    # Shift key while already hovering a card's Play button
    top = ctl.canvas.winfo_toplevel()
    ctl.play_btn.winfo_containing = lambda x, y: card["play"]
    ctl.play_btn.winfo_exists = lambda: True
    for fn in top._binds.get("<KeyPress-Shift_L>", []):
        fn(Event())
    check(card["play"].cget("cursor") == "exchange", "pressing Shift over a card's Play shows the loop cursor")
    for fn in top._binds.get("<KeyRelease-Shift_L>", []):
        fn(Event())
    check(card["play"].cget("cursor") == "hand2", "...and releasing Shift restores it")

    # region snaps
    check(card["start_rsnap"].cget("state") == "disabled", "region snaps are disabled before stems exist")
    ctl._set_regions([{"start": 0.0, "end": 10.0, "kind": "novocal"}, {"start": 10.0, "end": 20.0, "kind": "vocal"},
                      {"start": 20.0, "end": 100.0, "kind": "mixed"}])
    ctl.render_waveform()
    card = panel.cards[a["id"]]
    check(card["start_rsnap"].cget("state") == "normal", "...and enabled once regions exist")
    card["start_rsnap"]._cfg["command"]()
    check(ctl.mark_by_id(a["id"])["start"] == 10.0, "[ sets Start to the start of its stem region")
    panel.cards[a["id"]]["end_rsnap"]._cfg["command"]()
    check(ctl.mark_by_id(a["id"])["end"] == 20.0, "] sets End to the end of its stem region")
    panel.cards[a["id"]]["end_rsnap"]._cfg["command"]()
    check(ctl.mark_by_id(a["id"])["end"] == 100.0, "] again steps to the end of the next region")

    # skip buttons: click = 5 s, Shift = stem region edge, Ctrl = audio edge
    ctl.selected = None
    ctl.stop_play()
    ctl.cursor_time = 15.0
    ctl.skip_play(-5.0)
    check(abs(ctl.cursor_time - 10.0) < 1e-9, "\u25c0\u25c0 click: back 5 s")
    ctl.cursor_time = 15.0
    ctl.play_back_btn.fire("<ButtonRelease-1>", Event(state=0x0001)); ctl.skip_play(-5.0)
    check(abs(ctl.cursor_time - 10.0) < 1e-9, "Shift+\u25c0\u25c0: start of the stem region")
    ctl.play_back_btn.fire("<ButtonRelease-1>", Event(state=0x0001)); ctl.skip_play(-5.0)
    check(ctl.cursor_time == 0.0, "...again: the region before")
    ctl.cursor_time = 15.0
    ctl.play_fwd_btn.fire("<ButtonRelease-1>", Event(state=0x0001)); ctl.skip_play(5.0)
    check(abs(ctl.cursor_time - 20.0) < 1e-9, "Shift+\u25b6\u25b6: end of the stem region")
    ctl.play_fwd_btn.fire("<ButtonRelease-1>", Event(state=0x0004)); ctl.skip_play(5.0)
    check(ctl.cursor_time == 100.0, "Ctrl+\u25b6\u25b6: end of the audio")
    ctl.skip_play(5.0)
    check(ctl.cursor_time == 100.0, "a plain click past the end stays at the end")
    ctl.play_back_btn.fire("<ButtonRelease-1>", Event(state=0x0004)); ctl.skip_play(-5.0)
    check(ctl.cursor_time == 0.0, "Ctrl+\u25c0\u25c0: start of the audio")
    ctl.skip_play(-5.0)
    check(ctl.cursor_time == 0.0, "...and a plain click before the start stays at 0:00")
    ctl.skip_play(5.0)
    check(abs(ctl.cursor_time - 5.0) < 1e-9, "modifiers are only used for the click they were held on")

    # volume
    check(ctl.volume == 1.0 and ctl.vol_label.cget("text") == "vol 100%", "volume starts at 100%")
    ctl.change_volume(-0.1); ctl.change_volume(-0.1)
    check(abs(ctl.volume - 0.8) < 1e-9 and ctl.engine.volume == ctl.volume and ctl.vol_label.cget("text") == "vol 80%",
          "volume - lowers it and the engine uses it")
    check(abs(float(utils.get_preference("playback_volume")) - 0.8) < 1e-9, "the volume is remembered")
    ctl2, *_ = bare_controller(wt, fresh_copy(media, "round5b"))
    check(abs(ctl2.volume - 0.8) < 1e-9, "...and restored for the next file")
    for _ in range(30):
        ctl.change_volume(0.1)
    check(ctl.volume == 2.0 and ctl.vol_up_btn.cget("state") == "disabled", "volume tops out at 200%")
    utils.set_preference("playback_volume", 1.0)
    eng = th.SoundDevicePlaybackEngine()
    eng.set_volume(0.5)
    check(eng.volume == 0.5, "real engines accept a volume")

    # zoom out one step past fit
    ctl.view_start, ctl.view_end = 0.0, 100.0
    ctl.zoom_waveform("out")
    check(ctl.view_start == 0.0 and abs(ctl.view_end - 110.0) < 1e-9, "zooming out from fit adds 10% past the end")
    ctl.zoom_waveform("out")
    check(abs(ctl.view_end - 110.0) < 1e-9, "...only one extra step")
    check(abs(ctl._time_at_x(799) - 100.0) < 1e-9, "clicks past the end map to the end of the audio")
    p0, p1 = ctl._peaks_span
    check(p1 == 100.0, "the waveform data stops at the end of the audio")
    check([it for it in canvas.items if "past_end" in (it.get("tags") or ())], "the area past the end is shaded")
    ctl.zoom_waveform("in")
    check(ctl.view_end <= 100.0, "zooming in comes back inside the audio")


def test_round7(th, aa, wt, media):
    print("\n-- card delete focus, unassigned marks on close, stem smoothing, range from stem --")
    import utils
    path = fresh_copy(media, "round7")
    ctl, canvas, text, tab = bare_controller(wt, path)
    tr = ctl._new_track("Lyrics")
    a = ctl._add_mark("range", 2.0, 3.0, label="a", track_id=tr["id"])
    b = ctl._add_mark("range", 4.0, 5.0, label="b", track_id=tr["id"])
    c = ctl._add_mark("range", 6.0, 7.0, label="c", track_id=tr["id"])
    ctl.selected = ("mark", c["id"]); ctl.render_waveform()
    ctl.panel.cards[c["id"]]["delete"]._cfg["command"]()
    check(ctl.selected == ("mark", b["id"]) and ctl.panel.mode == "track",
          "deleting the last card selects the previous card (the track keeps the focus)")
    ctl.panel.cards[a["id"]]["delete"]._cfg["command"]()
    check(ctl.selected == ("mark", b["id"]), "deleting a middle/first card selects the next one")
    ctl.panel.cards[b["id"]]["delete"]._cfg["command"]()
    check(ctl.selected == ("track", tr["id"]) and ctl.panel.mode == "track",
          "deleting the only card leaves the track selected")

    # unassigned (work-area) marks when closing
    check(tab.before_close_hook == ctl.before_close, "audio tabs ask before closing")
    check(ctl.before_close() is True, "with no unassigned marks there's nothing to ask")
    ctl._add_mark("point", 10.0, None); ctl._add_mark("range", 20.0, 25.0)
    asked = []
    ctl.ask_unassigned = lambda n: asked.append(n) or "cancel"
    check(ctl.before_close() is False and asked == [2], "Cancel keeps the tab open")
    ctl.ask_unassigned = lambda n: "leave"
    check(ctl.before_close() is True and len([m for m in ctl.marks if m["track_id"] is None]) == 2,
          "'Leave them for next time' keeps them where they are")
    ctl.ask_unassigned = lambda n: "track"
    check(ctl.before_close() is True, "'Save into a new track' lets the close go ahead")
    new_track = ctl.tracks[-1]
    check(new_track["name"] == ctl.UNASSIGNED_TRACK_NAME
          and len(ctl.track_marks(new_track["id"])) == 2 and not [m for m in ctl.marks if m["track_id"] is None],
          "...and moves them into a new track")
    ctl.undo_marks()
    ctl.ask_unassigned = lambda n: "delete"
    ctl.before_close()
    check(not [m for m in ctl.marks if m["track_id"] is None], "'Delete them' removes them")

    import tracked
    order = []
    fake_tab = FakeTab()
    fake_tab.before_close_hook = lambda: order.append("hook") or False
    fake_tab.destroy = lambda: order.append("destroyed")
    app = types.SimpleNamespace(current_tab=lambda: fake_tab, notebook=FakeWidget(), tabs=[fake_tab], _debug_tab=None)
    tracked.EditorTab = FakeWidget
    tracked.EditorApp.close_tab(app, fake_tab)
    check(order == ["hook"], "closing the tab asks the hook first, and a cancel stops the close")

    # stem smoothing
    regions = [{"start": 0.0, "end": 5.0, "kind": "vocal"}, {"start": 5.0, "end": 5.4, "kind": "novocal"},
               {"start": 5.4, "end": 9.0, "kind": "vocal"}, {"start": 9.0, "end": 9.6, "kind": "mixed"},
               {"start": 9.6, "end": 20.0, "kind": "novocal"}]
    sm = aa.smooth_regions(regions, 1.0)
    check([(r["start"], r["end"], r["kind"]) for r in sm] == [(0.0, 9.0, "vocal"), (9.0, 20.0, "novocal")],
          "short changes (<1 s) are merged: a gap inside a vocal run disappears, a blip joins the longer side")
    check(len(aa.smooth_regions(regions, 0)) == 5, "a threshold of 0 keeps every change")
    check(abs(utils.get_stem_min_seconds() - 1.0) < 1e-9, "the threshold preference defaults to 1 second")
    ctl._set_regions(regions)
    check(len(ctl.regions) == 2 and len(ctl._raw_regions) == 5,
          "the waveform uses the smoothed regions (the analysis itself is kept)")
    utils.set_preference("stem_min_seconds", 0.5)
    ctl.resmooth_regions()
    check([r["kind"] for r in ctl.regions] == ["vocal", "mixed", "novocal"],
          "changing the preference re-smooths right away (0.5 s: the 0.4 s gap merges, the 0.6 s blip stays)")
    utils.set_preference("stem_min_seconds", 1.0)
    ctl.resmooth_regions()

    # new range from the stem at the @cursor
    ctl.cursor_time = 12.0
    ctl.stems_menu.entries.clear()
    ctl._fill_stems_menu()
    entry = next(e for e in ctl.stems_menu.entries if e["label"].startswith("New range from the stem at @cursor"))
    check("Instrumental" in entry["label"], "the Stems menu offers a range from the stem under the @cursor")
    entry["command"]()
    m = ctl.mark_by_id(ctl.selected[1])
    check((m["type"], m["start"], m["end"], m["track_id"]) == ("range", 9.0, 20.0, None),
          "...which spans that stem region and is selected")


def test_round8(th, aa, wt, media):
    print("\n-- stem colors, combined stem tracks, genre/mood, position entry, navigator --")
    import utils
    path = fresh_copy(media, "round8")
    ctl, canvas, text, tab = bare_controller(wt, path)
    check(wt.REGION_COLORS["vocal"] == "#229954", "the default vocal green is darker (stands apart from teal)")
    ctl._set_regions([{"start": 0.0, "end": 10.0, "kind": "vocal"}, {"start": 10.0, "end": 20.0, "kind": "mixed"},
                      {"start": 20.0, "end": 30.0, "kind": "novocal"}, {"start": 30.0, "end": 40.0, "kind": "mixed"},
                      {"start": 40.0, "end": 100.0, "kind": "vocal"}])
    ctl.render_waveform()
    legend_names = [it["text"] for it in canvas.items if "legend" in (it.get("tags") or ()) and it["kind"] == "text"]
    check("instrumental" in legend_names and "non-vocal" not in legend_names, "the color key says 'instrumental'")
    x0, x1, kind = next(h for h in ctl._legend_hits if h[2] == "novocal")
    y = ctl._track_layout()["row_top"] + 5
    ctl._on_waveform_motion(Event(x=(x0 + x1) // 2, y=y))
    check(canvas.cursor == "hand2", "the color key shows a hand cursor")
    ctl._on_waveform_press(Event(x=(x0 + x1) // 2, y=y))
    picker = ctl._color_picker
    check(picker is not None and picker.color == "#3498db", "clicking a color in the key opens a color picker on it")
    picker.hex_entry.type_text("#aa5500"); picker._from_hex(); picker.ok()
    check(ctl.region_colors["novocal"] == "#aa5500" and utils.get_preference("stem_colors") == {"novocal": "#aa5500"},
          "the new color is used right away and saved as a preference")
    colors = {it.get("fill") for it in canvas.items if it["kind"] == "line"}
    check("#aa5500" in colors, "the waveform is redrawn in the new color")
    ctl2, *_ = bare_controller(wt, fresh_copy(media, "round8b"))
    check(ctl2.region_colors["novocal"] == "#aa5500", "...and other audio tabs use it too")
    ctl._on_waveform_press(Event(x=(x0 + x1) // 2, y=y))
    ctl._color_picker.set_hsv(120, 50, 50)
    ctl._color_picker.cancel()
    check(ctl.region_colors["novocal"] == "#aa5500", "cancelling the picker changes nothing")
    ctl.reset_stem_colors()
    check(ctl.region_colors == wt.REGION_COLORS, "Stems \u25be > Reset stem colors restores the defaults")

    # combined stem tracks
    ctl._merge_var.set(True)
    t = ctl.create_combined_stem_track("Vocal or Mixed", ("vocal", "mixed"))
    spans = [(m["start"], m["end"]) for m in ctl.track_marks(t["id"])]
    check(spans == [(0.0, 20.0), (30.0, 100.0)], "'Vocal or Mixed' with merging: touching vocal+mixed become one range")
    check(t["color"] == ctl.region_colors["vocal"], "...colored like vocal")
    ctl.undo_marks()
    ctl._merge_var.set(False); ctl._on_merge_toggled()
    t = ctl.create_combined_stem_track("Instrumental or Mixed", ("novocal", "mixed"))
    spans = [(m["start"], m["end"]) for m in ctl.track_marks(t["id"])]
    check(spans == [(10.0, 20.0), (20.0, 30.0), (30.0, 40.0)],
          "'Instrumental or Mixed' without merging: one range per region")
    check(utils.get_preference("stem_track_merge") is False, "the merge choice is remembered")
    ctl.stems_menu.entries.clear(); ctl._fill_stems_menu()
    labels = [e["label"] for e in ctl.stems_menu.entries]
    check(any("Vocal or Mixed" in l for l in labels) and any("Instrumental or Mixed" in l for l in labels)
          and "Reset stem colors" in labels, "the Stems menu has the combined options and Reset stem colors")
    utils.set_preference("stem_track_merge", True)

    # genre / mood
    f = dict(tempo=128, mean_rms=0.12, mean_cent=3000, mean_bw=2500, mean_contrast=21, mean_zcr=0.06, percussiveness=4)
    r = aa.score_genre_mood(f)
    check(r["genre"] in ("electronic / dance", "pop") and r["mood"] in aa.MOOD_PALETTES and r["palette"],
          "the genre/mood rules give a genre, a mood and its palette")
    slow = dict(tempo=70, mean_rms=0.03, mean_cent=800, mean_bw=1500, mean_contrast=10, mean_zcr=0.03, percussiveness=1)
    check(aa.score_genre_mood(slow)["mood"] == "melancholic / reflective", "quiet, slow, dark audio reads as melancholic")
    check(aa.score_genre_mood(slow, "rap beat flow mic rhyme street hood")["genre"] == "hip-hop / rap",
          "lyrics (e.g. from Transcribe) nudge the genre")
    ctl._add_mark("range", 1.0, 2.0, label="dance tonight baby")
    seen = {}
    real_avail, real_est = aa.genre_mood_available, aa.estimate_genre_mood
    aa.genre_mood_available = lambda: True
    aa.estimate_genre_mood = lambda path, lyrics="", cb=None: seen.update(lyrics=lyrics) or r
    try:
        ctl.run_genre_mood()
        run_afters()
    finally:
        aa.genre_mood_available, aa.estimate_genre_mood = real_avail, real_est
    check("dance tonight baby" in seen.get("lyrics", ""), "the Mood button passes the transcribed labels along")
    check("Genre / mood estimate" in ctl.info_text and r["genre"] in ctl.analysis_status_var.get(),
          "its result goes to the text panel and the status row")
    check(th.load_cache(path).get("genre_mood", {}).get("genre") == r["genre"], "...and is cached with the file")
    calls = {"n": 0}
    aa.genre_mood_available = lambda: True
    aa.estimate_genre_mood = lambda path, lyrics="", cb=None: calls.update(n=calls["n"] + 1) or r
    saved_info = ctl.info_text
    try:
        ctl.info_text = ""
        ctl.run_genre_mood()
        run_afters()
        check(calls["n"] == 0 and "cached result" in ctl.info_text,
              "Mood again: the cached result is shown, not recomputed")
        ctl.mood_btn.fire("<ButtonRelease-1>", Event(state=0x0001))   # Shift+click
        ctl.run_genre_mood()
        run_afters()
        check(calls["n"] == 1, "Shift+click on Mood re-runs the estimate anyway")
        ctl.mood_btn.fire("<ButtonRelease-1>", Event(state=0))
        ctl.run_genre_mood()
        run_afters()
        check(calls["n"] == 1, "...and a plain click afterwards uses the cache again")
        later = time.time() + 7
        os.utime(path, (later, later))
        ctl.run_genre_mood()
        run_afters()
        check(calls["n"] == 2, "a changed audio timestamp makes Mood recompute")
    finally:
        aa.genre_mood_available, aa.estimate_genre_mood = real_avail, real_est
        ctl.info_text = saved_info + ctl.info_text

    # position entry
    ctl.pos_entry.type_text("1:05.5")
    ctl.pos_entry.fire("<Return>")
    check(abs(ctl.cursor_time - 65.5) < 1e-9, "typing a time in the position box + Enter moves the @cursor")
    ctl.pos_entry.type_text("999")
    ctl.pos_entry.fire("<Return>")
    check(ctl.cursor_time == 100.0, "...clamped to the end of the audio")
    ctl.pos_entry.type_text("abc")
    ctl.pos_entry.fire("<Return>")
    check(ctl.cursor_time == 100.0 and ctl.pos_entry.get() == "1:40.000", "junk is rejected and the box restored")

    # navigator
    ctl.view_start, ctl.view_end = 0.0, 25.0
    ctl._refresh_view_from_cache()
    w, nx0, nx1 = ctl._nav_geometry()
    check(abs((nx1 - nx0) / w - 0.25) < 0.01, "the navigator thumb is the visible fraction of the audio")
    ctl.nav.fire("<ButtonPress-1>", Event(x=int(nx0) + 5, y=5))
    ctl.nav.fire("<B1-Motion>", Event(x=int(nx0) + 5 + int(w * 0.5), y=5))
    check(abs(ctl.view_start - 50.0) < 1.0 and abs((ctl.view_end - ctl.view_start) - 25.0) < 1e-9,
          "dragging the thumb scrolls the view, keeping the zoom")
    ctl.nav.fire("<B1-Motion>", Event(x=w * 5, y=5))
    check(abs(ctl.view_end - 100.0) < 1e-9, "...and stops at the end")
    ctl.nav.fire("<ButtonPress-1>", Event(x=5, y=5))
    check(ctl.view_start == 0.0, "clicking beside the thumb jumps the view there")
    info = ctl.info_text
    check("{cyan}M{blue}=point mark at the @cursor" in info, "the text panel help mentions M")


def test_round9(th, aa, wt, media):
    print("\n-- wrapping text, Split menu, word timing, live color preview, whole transcription, lyrics import --")
    import timing_panel as tp
    check([th.syllable_count(w) for w in ("love", "little", "beautiful", "wanted", "played", "I")] == [1, 2, 3, 2, 1, 1],
          "syllable estimates for common words")
    m = {"id": "x", "type": "range", "start": 0.0, "end": 10.0, "label": "Hello, beautiful  world. Yes"}
    plan = th.plan_pieces(m, th.word_spans(m["label"]))
    texts = [p[2] for p in plan]
    check(texts == ["Hello,", "beautiful", "world.", "Yes"], "punctuation stays with its word")
    durs = [e - s0 for s0, e, _ in plan]
    check(durs[1] > durs[0] > durs[3], "longer words (more syllables) get more time")
    gaps = [plan[i + 1][0] - plan[i][1] for i in range(3)]
    check(all(g > 0 for g in gaps) and gaps[2] > gaps[0], "commas, double spaces and full stops leave gaps (full stop longest)")
    check(plan[0][0] == 0.0 and plan[-1][1] == 10.0, "the pieces still span the whole range")
    check(th.plan_pieces({"id": "p", "type": "point", "start": 4.0, "end": None, "label": "a b"},
                         th.word_spans("a b")) == [(4.0, None, "a"), (4.0, None, "b")],
          "a point mark's words all keep its time")

    path = fresh_copy(media, "round9")
    ctl, canvas, text, tab = bare_controller(wt, path)
    tr = ctl._new_track("Lyrics")
    mk = ctl._add_mark("range", 10.0, 20.0, label="one two three four five", track_id=tr["id"])
    ctl.selected = ("mark", mk["id"]); ctl.render_waveform()
    card = ctl.panel.cards[mk["id"]]
    check(isinstance(card["text"], tp.WrapField) and card["text"].widget.cget("wrap") == "word",
          "the card's text field wraps long text")
    card["text"].insert("end", "\nsix")
    card["text"].fit()
    check(card["text"].widget.cget("height") == 2, "...and grows with it")
    ctl.panel._set_entry(card["text"], "one two three four five")
    card["text"].select_range(8, 18)                 # "three four"
    menu = card["split_menu"]
    menu.entries.clear()
    ctl.panel._fill_split_menu(mk["id"], menu)
    check([e["label"] for e in menu.entries] == ["Split at cursor", "Split selected phrase", "Split into words (5)"]
          and menu.entry("Split selected phrase").get("state") == "normal",
          "Split \u25be offers cursor / selected phrase / words")
    menu.entry("Split selected phrase")["command"]()
    pieces = ctl.track_marks(tr["id"])
    check([p["label"] for p in pieces] == ["one two", "three four", "five"],
          "'Split selected phrase' makes before / selection / after")
    check(pieces[0]["start"] == 10.0 and pieces[-1]["end"] == 20.0, "...spanning the original range")
    ctl.undo_marks()
    check(len(ctl.track_marks(tr["id"])) == 1, "one undo restores the card")
    card = ctl.panel.cards[mk["id"]]
    menu = card["split_menu"]; menu.entries.clear()
    card["text"].select_range(0, 3)                  # the first word only: no "before" piece
    ctl.panel._fill_split_menu(mk["id"], menu)
    menu.entry("Split selected phrase")["command"]()
    check([p["label"] for p in ctl.track_marks(tr["id"])] == ["one", "two three four five"],
          "a selection at the start makes just two pieces")
    ctl.undo_marks()
    card = ctl.panel.cards[mk["id"]]
    menu = card["split_menu"]; menu.entries.clear()
    card["text"].widget.tag_remove("sel")
    ctl.panel._fill_split_menu(mk["id"], menu)
    check(menu.entry("Split selected phrase").get("state") == "disabled", "no selection: phrase split is disabled")
    menu.entry("Split into words (5)")["command"]()
    words = ctl.track_marks(tr["id"])
    check([p["label"] for p in words] == ["one", "two", "three", "four", "five"], "'Split into words' makes one card per word")
    check(words[0]["start"] == 10.0 and words[-1]["end"] == 20.0
          and all(a["end"] <= b["start"] for a, b in zip(words, words[1:])), "...in order, within the range")

    # live color preview
    ctl._set_regions([{"start": 0.0, "end": 50.0, "kind": "vocal"}, {"start": 50.0, "end": 100.0, "kind": "novocal"}])
    picker = ctl.pick_stem_color("vocal")
    picker.set_hsv(0, 100, 100)                     # pure red
    run_afters()
    check(ctl.region_colors["vocal"] == "#ff0000" and "#ff0000" in {it.get("fill") for it in canvas.items},
          "moving the sliders recolors the waveform live")
    check(picker.hex_entry.get() == "#ff0000", "the hex field follows the sliders")
    picker.cancel()
    check(ctl.region_colors["vocal"] == wt.REGION_COLORS["vocal"], "Cancel puts the old color back")
    picker = ctl.pick_stem_color("vocal")
    picker.hex_entry.type_text("00ff00"); picker._from_hex()
    picker.ok()
    import utils
    check(ctl.region_colors["vocal"] == "#00ff00" and utils.get_preference("stem_colors", {}).get("vocal") == "#00ff00",
          "typing a hex value and OK keeps (and saves) it")
    ctl.reset_stem_colors()

    # whole-audio transcription
    calls, WhisperModel = install_fake_ml()
    aa._probe_cache.update({"faster_whisper": True, "whisperx": False, "whisper": False, "demucs": False})
    real = aa.transcribe_range
    aa.transcribe_range = lambda *a, **k: {"text": "la la hey", "segments": [(1.0, 4.0, "la la"), (6.0, 7.5, "hey")],
                                           "model": "base", "backend": "fake", "source": "mix",
                                           "seconds_voiced": 5.0, "elapsed": 0.1}
    try:
        ctl.selected = None
        ctl.transcribe_selected()               # askyesno answers yes in the fake messagebox
        run_afters()
    finally:
        aa.transcribe_range = real
    tt = ctl.tracks[-1]
    got = [(m["start"], m["end"], m["label"]) for m in ctl.track_marks(tt["id"])]
    check(tt["name"] == "Transcript" and got == [(1.0, 4.0, "la la"), (6.0, 7.5, "hey")],
          "with nothing selected, Transcribe does the whole audio: one card per Whisper phrase, at its times")

    # lyrics / labels import
    lrc = os.path.join(TMP, "song-lyrics.lrc")
    open(lrc, "w").write("[ti:Song]\n[offset:+500]\n[00:02.50]First line\n[00:05.50]Second <00:06.00>line\n[00:08.50]\n")
    t = ctl.import_text_track(lrc)
    got = [(round(m["start"], 2), round(m["end"], 2), m["label"]) for m in ctl.track_marks(t["id"])]
    check(t["name"] == "song-lyrics" and got == [(2.0, 5.0, "First line"), (5.0, 8.0, "Second line")],
          "an LRC file becomes one card per line (offset and word stamps handled; a blank line ends the last)")
    aud = os.path.join(TMP, "labels.txt")
    open(aud, "w").write("1.5\t3.0\tverse\n4.0\t4.0\tbeat\n")
    t = ctl.import_text_track(aud)
    got = [(m["type"], m["start"], m["label"]) for m in ctl.track_marks(t["id"])]
    check(got == [("range", 1.5, "verse"), ("point", 4.0, "beat")], "Audacity labels import as ranges and points")
    plain = os.path.join(TMP, "words.txt")
    open(plain, "w").write("Hello world\nsecond line\n")
    t = ctl.import_text_track(plain)
    cards = ctl.track_marks(t["id"])
    check(len(cards) == 1 and (cards[0]["start"], cards[0]["end"]) == (0.0, 100.0)
          and cards[0]["label"] == "Hello world\nsecond line",
          "plain lyrics become one card over the whole audio (line breaks kept)")
    ctl.split_mark_into(cards[0]["id"], th.word_spans(cards[0]["label"]))
    parts = ctl.track_marks(t["id"])
    check(parts[2]["start"] - parts[1]["end"] > parts[1]["start"] - parts[0]["end"],
          "...and splitting it into words leaves a bigger gap at the line break")

    class DropEv:
        def __init__(self, data, y):
            self.data, self.x_root, self.y_root, self.action = data, 10, y, "copy"
    opened = []
    canvas.winfo_toplevel()._on_drop = lambda ev: opened.append(ev.data)
    canvas.winfo_rooty = lambda: 0
    canvas.tk = types.SimpleNamespace(splitlist=lambda d: d.split("|"))
    layout = ctl._track_layout()
    n = len(ctl.tracks)
    ctl._on_file_drop(DropEv(aud, layout["row_top"] + 3))
    check(len(ctl.tracks) == n + 1 and not opened, "dropping a text file on the drop row imports it as a track")
    ctl._on_file_drop(DropEv(aud, 10))
    check(len(ctl.tracks) == n + 1 and opened == [aud], "dropped elsewhere on the waveform, it opens as a tab as usual")


def test_title_dirty_autosave(th, wt, media):
    print("\n-- window title duration, dirty tabs, save hook, auto-save --")
    import tracked
    import utils
    path = fresh_copy(media, "savetest")
    ctl, canvas, text, tab = open_controller(wt, path)
    check(tab.title_detail == th.format_time_ms(ctl.audio_duration) and tab.title_refreshes >= 1,
          "the audio duration is handed to the window title once loaded")
    check(tab.save_hook == ctl.save_marks_now, "audio tabs save through their own hook")

    class App:
        pass
    app = App()
    app.status = FakeWidget()
    app._debug_tab = None
    app._update_title = lambda: None
    app._rebuild_recent_menu = lambda: None
    app.tabs = [tab]
    app.after = lambda ms, fn: None
    app._save_tab = lambda t, interactive=True: tracked.EditorApp._save_tab(app, t, interactive)
    app.set_status = lambda msg: tracked.EditorApp.set_status(app, msg)
    app._autosave_tick = lambda: None
    tracked.EditorTab = FakeWidget
    tracked.abbreviated_name = lambda p, *a: os.path.basename(p or "Untitled")

    before = open(path, "rb").read()
    app._last_autosave = time.monotonic() - 1000   # an old global timer must not matter any more
    ctl._add_mark("point", 1.0, None)
    check(tab.dirty and tab.dirty_since is not None, "editing marks makes the tab dirty and starts its clock")
    tracked.EditorApp._autosave_tick(app)
    check(tab.dirty and th.load_marks(path) == [],
          "a change made just now is NOT saved early (the delay runs from the change)")
    ctl._add_mark("point", 2.0, None)
    first = tab.dirty_since
    check(tab.dirty_since == first, "further changes don't restart the clock (it counts from the first)")
    tab.dirty_since = time.monotonic() - 10.5
    tracked.EditorApp._autosave_tick(app)
    check(not tab.dirty and len(th.load_marks(path)) == 2, "10 s after the first change, auto-save saves the marks")
    check(open(path, "rb").read() == before, "auto-save never touches the audio file itself")

    txt = os.path.join(TMP, "notes.txt")
    open(txt, "w").write("old")
    ttab = FakeTab()
    ttab.filepath, ttab.save_hook, ttab.protect_file = txt, None, False
    ttab.get_content = lambda: "new text"
    ttab.dirty, ttab.dirty_since = True, time.monotonic() - 3
    app.tabs = [tab, ttab]
    tracked.add_recent = lambda p: None
    tracked.EditorApp._autosave_tick(app)
    check(open(txt).read() == "old", "each tab has its own clock: 3 s after its change, not yet")
    ttab.dirty_since = time.monotonic() - 11
    tracked.EditorApp._autosave_tick(app)
    check(open(txt).read() == "new text" and not ttab.dirty, "auto-save writes a text file's contents")

    untitled = FakeTab()
    untitled.filepath, untitled.save_hook, untitled.protect_file = None, None, False
    untitled.dirty, untitled.dirty_since = True, time.monotonic() - 100
    untitled.get_content = lambda: "x"
    app.tabs = [untitled]
    tracked.EditorApp._autosave_tick(app)
    check(untitled.dirty, "auto-save skips untitled tabs (no dialogs)")

    utils.set_preference("autosave_seconds", 0)
    ttab.dirty, ttab.dirty_since = True, time.monotonic() - 1000
    open(txt, "w").write("old")
    app.tabs = [ttab]
    tracked.EditorApp._autosave_tick(app)
    check(open(txt).read() == "old", "auto-save 0 = off")
    utils.set_preference("autosave_seconds", 10)
    check(utils.get_autosave_seconds() == 10, "the auto-save preference defaults to 10 seconds")


def test_stems_and_transcription(th, aa, wt, media):
    print("\n-- demucs stems, region colors, transcription (stand-in libraries) --")
    calls, WhisperModel = install_fake_ml(vocal_window=(2.0, 6.0))
    aa._probe_cache.update({"demucs": True, "torch": True, "faster_whisper": True, "whisperx": False, "whisper": False})
    path = fresh_copy(media, "stemtest")
    ctl, canvas, text, tab = open_controller(wt, path)
    run_afters()
    kinds = [(round(r["start"], 1), round(r["end"], 1), r["kind"]) for r in ctl.regions]
    check(calls["separations"] == 1, "stems are separated automatically on first open")
    check(kinds == [(0.0, 2.0, "novocal"), (2.0, 6.0, "vocal"), (6.0, 10.0, "novocal")],
          "regions follow the vocal stem")
    voc, nov = aa.stem_paths(path)
    check(voc.is_file() and nov.is_file(), "stem WAVs are saved next to the audio file")
    colors = {it.get("fill") for it in canvas.items if it["kind"] == "line"}
    check(wt.REGION_COLORS["vocal"] in colors and wt.REGION_COLORS["novocal"] in colors,
          "the waveform is drawn in region colors")
    info = text.get()
    check("vocal-only regions:" in info and "instrumental-only:" in info and "non-vocal" not in info,
          "region counts go to the text panel (as 'instrumental', not 'non-vocal')")
    check(th.load_regions(path) == ctl.regions, "regions are saved in the cache file")

    ctl2, _c, text2, _t = open_controller(wt, path)
    run_afters()
    check(calls["separations"] == 1 and ctl2.regions == ctl.regions, "reopening uses the cached regions (no demucs)")
    th.save_regions(path, [])
    ctl3, *_ = open_controller(wt, path)
    run_afters()
    check(calls["separations"] == 1 and len(ctl3.regions) == 3, "with regions gone, cached stem WAVs are reused")

    tr = ctl._new_track("Lyrics")
    rng = ctl._add_mark("range", 1.0, 8.0, track_id=tr["id"])
    ctl.selected = ("mark", rng["id"])
    ctl.model_var.set("small")
    ctl.transcribe_selected()
    run_afters()
    label = ctl.mark_by_id(rng["id"])["label"]
    check(label == "sung for 4.0 seconds", "only the vocal part of the range reaches Whisper; text becomes the label")
    check(ctl.panel.cards[rng["id"]]["text"].get() == label, "the panel card shows the transcription")
    check(WhisperModel.loads == 1, "the chosen model is loaded once")

    asked = []
    wt.messagebox.askyesno = lambda *a, **k: asked.append(a) or False
    ctl.transcribe_selected()
    run_afters()
    check(asked and ctl.mark_by_id(rng["id"])["label"] == label, "replacing existing text asks first (and No keeps it)")
    wt.messagebox.askyesno = lambda *a, **k: True

    quiet = ctl._add_mark("range", 7.0, 9.5, track_id=tr["id"])
    ctl.selected = ("mark", quiet["id"])
    ctl.transcribe_selected()
    run_afters()
    check(ctl.mark_by_id(quiet["id"])["label"] == "" and ctl.analysis_status_var.get() == "No vocals found in range",
          "a range with no vocals is reported and left unlabeled")
    ctl.transcribe_selected()
    run_afters()
    check(WhisperModel.loads == 1, "the model stays loaded between transcriptions")


def test_sash_hints_and_save_protection(media):
    print("\n-- panel sizing hints + audio-tab save protection --")
    import editor_tab
    import tracked
    calls = []

    class Paned:
        def sashpos(self, i, pos=None):
            calls.append(pos)
        def winfo_height(self):
            return 800

    fake = types.SimpleNamespace(filepath=os.path.join(TMP, "never-saved.wav"), paned=Paned(),
                                 min_sash=lambda: 180, preferred_sash=260, frame=FakeWidget(), _sash_ready=False)
    fake._sash_hint = lambda name: editor_tab.EditorTab._sash_hint(fake, name)
    editor_tab.EditorTab._restore_sash(fake)
    check(calls[-1] == 260, "a file with no saved sash uses the plugin's preferred height")
    import utils
    utils.set_sash_pos(fake.filepath, 60)
    editor_tab.EditorTab._restore_sash(fake)
    check(calls[-1] == 180, "a saved sash smaller than the plugin's minimum is raised to the minimum")

    victim = os.path.join(TMP, "protected.wav")
    shutil.copyfile(media, victim)
    before = open(victim, "rb").read()
    app = types.SimpleNamespace(status=FakeWidget())
    tab = types.SimpleNamespace(filepath=victim, protect_file=True, get_content=lambda: "TEXT")
    app.current_tab = lambda: tab
    app._save_tab = lambda t, interactive=True: tracked.EditorApp._save_tab(app, t, interactive)
    app.set_status = lambda msg: tracked.EditorApp.set_status(app, msg)
    tracked.EditorTab = types.SimpleNamespace  # so the isinstance() check accepts our stand-in tab
    result = tracked.EditorApp.save_file(app)
    check(result is False and open(victim, "rb").read() == before, "File > Save never writes text over an audio file")


def test_debug_level_cli():
    print("\n-- debug level preference + command line --")
    import tracked
    import utils
    check(utils.get_default_debug_level() == 10, "the default debug level preference is 10")
    check(tracked.parse_args(["x"])[2] is None, "no flag -> use the stored preference")
    check(tracked.parse_args(["x", "-debug", "5", "a.mp3"])[1:] == (False, 5)
          and tracked.parse_args(["x", "-debug", "5", "a.mp3"])[0] == ["a.mp3"], "-debug N overrides for this run")
    check(tracked.parse_args(["x", "-nodebug"])[2] == 0, "-nodebug turns it off for this run")
    check(utils.get_default_debug_level() == 10, "one-run overrides don't change the stored default")
    tracked.parse_args(["x", "-debug-default", "3"])
    check(utils.get_default_debug_level() == 3, "-debug-default N stores a new default")
    tracked.parse_args(["x", "-debug-default"])
    check(utils.get_default_debug_level() == 10, "-debug-default alone resets it to 10")


def test_image_viewer():
    print("\n-- image tab: zoom in/out/fit/100%, wheel zoom at the pointer, pan --")
    try:
        from PIL import Image, ImageTk
    except ImportError:
        print("  SKIP: Pillow not installed")
        return
    import image_tab
    path = os.path.join(TMP, "picture.png")
    Image.new("RGB", (1600, 1000), (200, 50, 50)).save(path)
    drawn = []
    real_photo = ImageTk.PhotoImage
    ImageTk.PhotoImage = lambda img, master=None: drawn.append(img.size) or img   # no real Tk here
    try:
        canvas, text, tab = FakeCanvas(FakeWidget()), FakeText(), FakeWidget()
        check(image_tab.onload(path, canvas=canvas, text=text, tab=tab), "image_tab claims a PNG")
        v = canvas._image_viewer
        run_afters()
        check(v.fit and abs(v.scale - 0.2) < 1e-9, "opens fitted to the panel (800x200 canvas -> 20%)")
        check(v.zoom_var.get() == "20% (fit)", "the zoom label shows the percentage")
        check(drawn and drawn[-1] == (320, 200), "fit draws the whole image at the fitted size")
        check(callable(tab.min_sash) and callable(tab.preferred_sash), "the image tab gives sash size hints")
        check(getattr(tab, "protect_file", False), "an image's description text can never be saved over it")

        v.zoom_in()
        check(not v.fit and abs(v.scale - 0.25) < 1e-9, "+ zooms in by 1.25x and leaves fit mode")
        v.zoom_actual()
        check(v.scale == 1.0 and drawn[-1] == (801, 201), "100% draws only the visible part at full size")
        ix = v.cx + (100 - 400) / v.scale
        canvas.fire("<MouseWheel>", Event(x=100, y=50, delta=120))
        check(abs(v.scale - 1.25) < 1e-9, "wheel up over the image zooms in")
        check(abs((v.cx + (100 - 400) / v.scale) - ix) < 1e-6, "wheel zoom keeps the point under the mouse in place")
        canvas.fire("<Button-5>", Event(x=100, y=50, num=5))
        check(abs(v.scale - 1.0) < 1e-9, "X11 wheel down (Button-5) zooms out")

        cx0 = v.cx
        canvas.fire("<ButtonPress-1>", Event(x=400, y=100))
        canvas.fire("<B1-Motion>", Event(x=300, y=100))
        canvas.fire("<ButtonRelease-1>", Event(x=300, y=100))
        check(abs(v.cx - (cx0 + 100)) < 1e-9, "dragging pans the zoomed image")
        v.cx = -5000
        v.redraw()
        check(v.cx == 400.0, "panning can't drag the image off screen")
        for _ in range(40):
            v.zoom_out()
        check(abs(v.scale - v.min_scale()) < 1e-9, "zooming out stops at a minimum")
        v.zoom_fit()
        check(v.fit and abs(v.scale - 0.2) < 1e-9, "Fit returns to the fitted view")
        canvas.fire("<Double-Button-1>", Event(x=10, y=10))
        check(v.scale == 1.0, "double-click toggles Fit -> 100%")
    finally:
        ImageTk.PhotoImage = real_photo


def test_undo_routing_and_card_style(th, wt, media):
    print("\n-- undo/redo from anywhere in the audio tab; card styling; gutter alignment --")
    import timing_panel as tp
    import tracked
    path = fresh_copy(media, "undotest")
    ctl, canvas, text, tab = bare_controller(wt, path)
    tab._update_line_numbers = lambda: None
    check(tab.undo_hook == ctl.undo_marks and tab.redo_hook == ctl.redo_marks,
          "the audio tab routes Edit > Undo/Redo to the timing marks")
    tr = ctl._new_track("Lyrics")
    m = ctl._add_mark("range", 2.0, 4.0, label="la", track_id=tr["id"])
    ctl.selected = ("mark", m["id"]); ctl.render_waveform()
    ctl.set_mark_label(m["id"], "changed")
    text.fire("<Control-z>")
    check(ctl.mark_by_id(m["id"])["label"] == "la", "Ctrl+Z in the text panel undoes the last mark change")
    check(ctl.panel.mode == "track", "undo keeps the timing panel on the same track")
    text.fire("<Control-y>")
    check(ctl.mark_by_id(m["id"])["label"] == "changed", "Ctrl+Y in the text panel redoes it")
    card = ctl.panel.cards[m["id"]]
    card["text"].type_text("typed but not committed")
    card["text"].fire("<Control-z>")
    check(ctl.mark_by_id(m["id"])["label"] == "changed",
          "Ctrl+Z in a card field commits what was typed, then undoes that change")
    app = types.SimpleNamespace(current_tab=lambda: tab)
    tracked.EditorTab = types.SimpleNamespace
    tracked.EditorTab = FakeWidget   # so the isinstance() check accepts our stand-in tab
    tracked.EditorApp.redo(app)
    check(ctl.mark_by_id(m["id"])["label"] == "typed but not committed", "Edit > Redo reaches the marks too")
    tracked.EditorApp.undo(app)
    check(ctl.mark_by_id(m["id"])["label"] == "changed", "Edit > Undo reaches the marks too")

    card = ctl.panel.cards[m["id"]]
    buttons = [w for w in card["frame"].winfo_children()
               if "command" in w._cfg and w._cfg.get("text") != "\u2715"]   # delete is red on purpose
    tbtns = card["tbtns"]
    others = [b for b in buttons if b not in tbtns]
    check(others and all(b.cget("fg") == tp.FG and b.cget("bg") == tp.BTN_BG for b in others),
          "card buttons have explicit colors (visible without hovering)")
    check(tbtns and all(b.cget("bg") == card["frame"].cget("bg") and b.cget("fg") == tp.contrast_fg(b.cget("bg"))
                        for b in tbtns), "the Start/End buttons take the card's background")
    check(all(b.cget("cursor") == "hand2" for b in buttons), "card buttons show a hand cursor")
    b = buttons[0]
    b.fire("<Enter>")
    check(b.cget("bg") == tp.BTN_HOVER_BG, "hovering a card button highlights it")
    b.fire("<Leave>")
    check(b.cget("bg") == tp.BTN_BG, "...and leaving restores it")
    entries = [card["start"], card["end"], card["text"]]
    check(all(e.cget("fg") == tp.FG and e.cget("bg") == tp.ENTRY_BG for e in entries),
          "card fields have explicit text/background colors")
    ctl.render_waveform()
    run_afters()
    if hasattr(tab, "set_line_numbers_visible"):
        check(getattr(tab, "_line_numbers_shown", True) is False and not tab.gutter_offsets,
              "while cards are shown the tab's line numbers are hidden (each card shows its own #)")
        ctl.selected = None; ctl.render_waveform(); run_afters()
        check(getattr(tab, "_line_numbers_shown", True) is True, "...and back for the info text")
    else:
        check(not tab.gutter_offsets, "no gutter offsets while cards are shown")
    ctl.selected = None; ctl.render_waveform(); run_afters()
    check(not tab.gutter_offsets, "back in the info view, line numbers use normal centering")


def test_word_adjustments(th):
    print("\n-- syllable / time adjustments written into the lyrics: word {+1} / word {-0.1s} --")
    infos = th.word_infos("never gonna {+1} give fire{+1} you {-0.2s} up oh {-120ms} {1.5} x{ + 2 }")
    by_word = {i["word"]: i for i in infos}
    check(by_word["gonna"]["syllables"] == by_word["gonna"]["base"] + 1 and by_word["gonna"]["syl_adj"] == 1,
          "\"word {+1}\" adds a syllable to the word before it")
    check(by_word["fire"]["syl_adj"] == 1, "...also written without the space (\"fire{+1}\")")
    check(abs(by_word["you"]["time_adj"] + 0.2) < 1e-9 and by_word["you"]["syl_adj"] == 0,
          "\"{-0.2s}\" is a time adjustment (it has a unit), not syllables")
    check(abs(by_word["oh"]["time_adj"] + 0.12) < 1e-9, "milliseconds work too: {-120ms}")
    check("{1.5}" in by_word, "a number with no sign or with a decimal point but no unit is just text")
    check(by_word["x"]["syl_adj"] == 2, "spaces inside the braces are allowed: { + 2 }")
    check(len(infos) == 9, "the adjustments aren't counted as words")
    check(th.strip_adjustments("love {+0.5s} you{-1} {1.5}") == "love you {1.5}",
          "strip_adjustments leaves the plain lyrics (for the waveform and exports)")
    check(th.word_infos("rhythm {-1}")[0]["syllables"] == 0 and th.adjust_word("a {+1}", 0, syllables=-5)[0] == "a {-1}",
          "syllables can't go below zero")

    plain = {"type": "range", "start": 0.0, "end": 3.0, "label": "fire fire"}
    more = dict(plain, label="fire {+1} fire")
    p1 = th.plan_pieces(plain, th.word_spans(plain["label"]))
    p2 = th.plan_pieces(more, th.word_spans(more["label"]))
    check(abs(p1[0][1] - 1.5) < 1e-9 and p2[0][1] > 1.5 + 0.3, "a syllable adjustment gives that word a bigger share")
    check(p2[0][2] == "fire {+1}", "...and splitting into words keeps the adjustment with its word")
    timed = dict(plain, label="fire {+0.5s} fire")
    p3 = th.plan_pieces(timed, th.word_spans(timed["label"]))
    check(abs((p3[0][1] - p3[0][0]) - (p3[1][1] - p3[1][0]) - 0.5) < 1e-9 and p3[-1][1] == 3.0,
          "a time adjustment makes the word exactly that much longer than its syllables would")
    check(th.plan_pieces(dict(plain, label="fire {+3s} fire"), th.word_spans("fire {+3s} fire")) is None,
          "time adjustments that don't fit in the range make the split impossible (nothing changes)")
    split = th.plan_split(dict(plain, label="love {+1s} you so"))
    check(split and split["left"][2].startswith("love {+1s}") and split["left"][1] > 1.5,
          "Split at the middle honors the adjustments too")
    tm = th.word_timings({"type": "range", "start": 1.0, "end": 3.0, "label": "love {+0.5s} you"})
    check(len(tm) == 2 and abs(sum(i["seconds"] for i in tm) - 2.0) < 1e-9 and tm[0]["seconds"] > tm[1]["seconds"],
          "word_timings: each word's time as a word card")
    check(th.word_timings({"type": "point", "start": 1.0, "end": None, "label": "a b"})[0]["seconds"] is None,
          "...none for a point mark")

    text, span = th.adjust_word("beautiful day", 3, syllables=-1)
    check(text == "beautiful {-1} day" and span == (0, len("beautiful {-1}")), "adjust_word writes \"word {-1}\"")
    text2, _ = th.adjust_word(text, len("beautiful {-1} "), seconds=0.05)
    check(text2 == "beautiful {-1} day {+0.05s}", "...for the word at the index (here: day, a time step)")
    text3, _ = th.adjust_word(text2, 2, seconds=-0.1)
    check(text3 == "beautiful {-1} {-0.1s} day {+0.05s}", "syllable and time adjustments combine on one word")
    text4, _ = th.adjust_word(text3, 2, syllables=1)
    check(text4 == "beautiful {-0.1s} day {+0.05s}", "an adjustment that comes back to zero disappears")
    check(th.adjust_word(text4, 0, clear=True)[0] == "beautiful day {+0.05s}", "clear removes a word's adjustments")
    check(th.adjust_word("   ", 1, syllables=1) is None, "no word, no change")

    import xml.etree.ElementTree as ET
    out = os.path.join(TMP, "adj.xtiming")
    th.export_timing_tracks(out, [("T", [{"start": 0.0, "end": 1.0, "label": "fire {+1} {+0.2s}"}])])
    check(ET.parse(out).getroot().find(".//Effect").get("label") == "fire", "exports leave the adjustments out")
    out = os.path.join(TMP, "adj.lrc")
    th.export_timing_tracks(out, [("T", [{"start": 0.0, "end": 1.0, "label": "oh {-1}"}])])
    check(open(out).read().splitlines()[-1].endswith("]oh"), "...LRC too")
    check(th.next_voice_name([]) == "voice 1" and th.next_voice_name(["voice 1", "Lead", "Voice 7"]) == "voice 8",
          "new voices default to \"voice N\", numbered after the highest in use")


def test_voices(th, wt, media):
    print("\n-- voices: cards assigned to one or more user-defined voices --")
    path = fresh_copy(media, "voicetest")
    ctl, canvas, text, tab = bare_controller(wt, path)
    tr = ctl._new_track("Lyrics")
    a = ctl._add_mark("range", 2.0, 6.0, label="one two three four", track_id=tr["id"])
    b = ctl._add_mark("range", 7.0, 9.0, label="five", track_id=tr["id"])
    check(ctl.voices == [] and ctl.default_voice_name() == "voice 1", "no voices yet; the first default is \"voice 1\"")
    before = len(ctl._mark_history)
    name = ctl.add_voice(mark_id=a["id"])
    check(name == "voice 1" and ctl.voices == ["voice 1"] and a["voices"] == ["voice 1"],
          "a new voice is created on the fly and assigned to the card")
    check(len(ctl._mark_history) == before + 1, "...as one undo step")
    ctl.undo_marks()
    check(ctl.voices == [] and not ctl.mark_by_id(a["id"]).get("voices"), "undo removes the voice and the assignment")
    ctl.redo_marks()
    check(ctl.voices == ["voice 1"], "redo brings it back")
    asked = {}
    real_ask = wt.simpledialog.askstring
    try:
        wt.simpledialog.askstring = lambda title, prompt, **k: asked.update(k) or "Lead"
        check(ctl.ask_new_voice(b["id"]) == "Lead" and asked.get("initialvalue") == "voice 2",
              "New voice... suggests \"voice 2\"; typed text is used instead")
        wt.simpledialog.askstring = lambda *x, **k: "   "
        check(ctl.ask_new_voice(b["id"]) == "voice 2", "...an empty answer takes the default name")
        wt.simpledialog.askstring = lambda *x, **k: None
        check(ctl.ask_new_voice(b["id"]) is None and len(ctl.voices) == 3, "...Cancel creates nothing")
    finally:
        wt.simpledialog.askstring = real_ask
    check(ctl.mark_voices(b["id"]) == ["Lead", "voice 2"], "a card can have several voices")
    ctl.toggle_mark_voice(a["id"], "Lead")
    check(ctl.mark_voices(a["id"]) == ["voice 1", "Lead"], "toggling adds a voice (in the file's voice order)")
    ctl.toggle_mark_voice(a["id"], "voice 1")
    check(ctl.mark_voices(a["id"]) == ["Lead"], "...and toggling again removes it")

    ctl.selected = ("mark", a["id"])
    check(ctl.split_mark_into(a["id"], th.word_spans(a["label"])), "split into words")
    pieces = ctl.track_marks(tr["id"])[:4]
    check(all(p.get("voices") == ["Lead"] for p in pieces), "split pieces keep the card's voices")
    ctl.set_mark_voices(pieces[1]["id"], ["voice 1"])
    ctl.merge_mark_by_id(pieces[0]["id"], 1)
    check(ctl.mark_voices(pieces[0]["id"]) == ["Lead", "voice 1"], "merging combines the voices")

    ctl.rename_voice("voice 2", "Harmony")
    check("Harmony" in ctl.voices and ctl.mark_voices(b["id"]) == ["Lead", "Harmony"], "renaming a voice updates the cards")
    ctl.rename_voice("Harmony", "Lead")
    check(ctl.voices.count("Lead") == 1 and ctl.mark_voices(b["id"]) == ["Lead"],
          "renaming onto an existing name merges the two voices")
    ctl.delete_voice("voice 1")
    check("voice 1" not in ctl.voices and all("voice 1" not in (m.get("voices") or []) for m in ctl.marks),
          "deleting a voice takes it off every card")
    ctl.save_marks_now()
    check(th.load_voices(path) == ctl.voices and th.load_marks(path) == ctl.marks, "voices are saved in the sidecar")
    ctl2, *_ = bare_controller(wt, path)
    check(ctl2.voices == ctl.voices and ctl2.mark_voices(b["id"]) == ["Lead"], "...and come back when the file is reopened")

    # right-click on a range in the track: see / change its voices
    captured = []
    orig = wt.tk.Menu

    class Capture(orig):
        def __init__(self, *args, **kw):
            super().__init__(*args, **kw)
            captured.append(self)

    wt.tk.Menu = Capture
    try:
        layout = ctl._track_layout()
        ctl._on_waveform_right_click(Event(x=int(8.0 / 100 * 800), y=layout["track_top"] + 5))
    finally:
        wt.tk.Menu = orig
    main = next(m for m in captured if "Delete Mark" in m.labels())
    cascade = next(e for e in main.entries if e.get("kind") == "cascade")
    check(ctl.selected == ("mark", b["id"]) and cascade["label"] == "Voices: Lead",
          "right-clicking a range shows its voices in the menu")
    vmenu = cascade["menu"]
    checks = [e for e in vmenu.entries if e.get("kind") == "check"]
    check([e["label"] for e in checks] == ctl.voices and checks[0]["variable"].get() is True,
          "...with a check item per voice (checked when assigned)")
    check(any(l.startswith("New voice") for l in vmenu.labels()), "...and New voice...")
    vmenu.invoke_label("Lead")
    check(ctl.mark_voices(b["id"]) == [], "unchecking a voice there removes it from the range")

    # the card editor: Voice button, filter
    panel = ctl.panel
    ctl.set_mark_voices(b["id"], ["Lead"])
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    card = panel.cards[b["id"]]
    check(card["voice"].cget("text") == "Lead \u25be", "the card's Voice button shows its voices")
    ctl.set_mark_voices(b["id"], [])
    check(panel.cards[b["id"]]["voice"].cget("text") == "Voice \u25be", "...and follows changes")
    ctl.set_mark_voices(b["id"], ["Lead"])
    panel._fill_voice_menu(b["id"], card["voice_menu"])
    check([e["label"] for e in card["voice_menu"].entries if e.get("kind") == "check"] == ctl.voices,
          "the Voice \u25be menu lists the voices")
    ctl.set_mark_voices(ctl.track_marks(tr["id"])[0]["id"], [])     # one card without a voice
    shown_all = list(panel.cards)
    panel.voice_filter_var.set("Lead"); panel._on_voice_filter()
    check(list(panel.cards) == [m["id"] for m in ctl.track_marks(tr["id"]) if "Lead" in (m.get("voices") or [])]
          and len(panel.cards) < len(shown_all), "Show: <voice> limits the cards to that voice")
    check("of" in panel._header_label.cget("text"), "...and the header says how many are shown")
    panel.voice_filter_var.set("(no voice)")
    panel._on_voice_filter()
    check(len(panel.cards) == 1 and all(not ctl.mark_by_id(mid).get("voices") for mid in panel.cards),
          "Show: (no voice) shows the unassigned cards")
    panel.voice_filter_var.set("All voices"); panel._on_voice_filter()
    check(list(panel.cards) == shown_all, "All voices shows every card again")


def test_word_panel(th, wt, media):
    print("\n-- the card editor: syllables / time per word --")
    path = fresh_copy(media, "wordtest")
    ctl, canvas, text, tab = bare_controller(wt, path)
    tr = ctl._new_track("Lyrics")
    m = ctl._add_mark("range", 2.0, 6.0, label="beautiful day", track_id=tr["id"])
    panel = ctl.panel
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    tip = panel.word_tip_text(m["id"], 2)
    check(tip.startswith("\u201cbeautiful\u201d") and "syllable" in tip and "\u2248" in tip and " s as a word card" in tip,
          "hovering a word tells its syllables and its time as a word card")
    check(panel.word_tip_text(m["id"], len("beautiful d")).startswith("\u201cday\u201d"), "...for the word under the mouse")
    AFTERS.clear()
    panel._schedule_word_tip(m["id"], Event(x=5, y=5))
    check(len(AFTERS) == 1 and panel._word_tip is None, "the tip waits for the pointer to rest (nothing computed yet)")
    AFTERS.clear()
    panel.step_var.set("0.1")
    menu = panel.build_word_menu(m["id"], 2)
    labels = menu.labels()
    check(labels[0].startswith("\u201cbeautiful\u201d") and "One less syllable  {-1}" in labels
          and "Longer by 0.1 s  {+0.1s}" in labels, "right-clicking a word offers +/- syllables and +/- time (by the Step)")
    menu.invoke_label("One less syllable  {-1}")
    check(ctl.mark_by_id(m["id"])["label"] == "beautiful {-1} day", "...which writes the adjustment into the text")
    check(panel.cards[m["id"]]["text"].get() == "beautiful {-1} day", "...and shows it in the card right away")
    check(ctl.can_undo_marks(), "...as an undoable change")
    card = panel.cards[m["id"]]
    card["text"].icursor(len("beautiful {-1} da"))
    card["text"].fire("<Alt-Right>")
    check(ctl.mark_by_id(m["id"])["label"] == "beautiful {-1} day {+0.1s}", "Alt+Right: the word at the cursor gets longer")
    card["text"].icursor(1)
    card["text"].fire("<Alt-Up>")
    check(ctl.mark_by_id(m["id"])["label"] == "beautiful day {+0.1s}", "Alt+Up adds a syllable back (and a zero one vanishes)")
    menu = panel.build_word_menu(m["id"], len("beautiful d"))
    menu.invoke_label("Remove this word's adjustment")
    check(ctl.mark_by_id(m["id"])["label"] == "beautiful day", "Remove this word's adjustment clears it")
    ctl.undo_marks()
    check(ctl.mark_by_id(m["id"])["label"] == "beautiful day {+0.1s}", "undo steps back one adjustment at a time")
    ctl.render_waveform()
    labels_drawn = [it.get("text") for it in canvas.items if it["kind"] == "text"]
    check("beautiful day" in labels_drawn and not any("{+0.1s}" in (t or "") for t in labels_drawn),
          "the waveform label leaves the adjustments out")


LAYOUT_XML = """<?xml version="1.0" encoding="UTF-8"?>
<xrgb>
  <models>
    <model name="Arch1" DisplayAs="Arches" parm1="1" parm2="50" StringType="RGB Nodes"/>
    <model name="Arch2" DisplayAs="Arches" parm1="1" parm2="50" StringType="RGB Nodes"/>
    <model name="Arch10" DisplayAs="Arches" parm1="1" parm2="50" StringType="RGB Nodes"/>
    <model name="MegaTree" DisplayAs="Tree 360" parm1="16" parm2="100" StringType="RGB Nodes">
      <subModel name="Top" type="ranges"/>
    </model>
    <model name="Matrix" DisplayAs="Horiz Matrix" parm1="32" parm2="50" StringType="RGB Nodes"/>
    <model name="Window" DisplayAs="Window Frame" parm1="40" parm2="30" parm3="40" StringType="RGB Nodes"/>
    <model name="Star" DisplayAs="Star" parm1="1" parm2="100" StringType="RGB Nodes"/>
    <model name="Custom1" DisplayAs="Custom" parm1="4" parm2="2" CustomModel="1,2,,3;4,,5,6;6,,,"/>
    <model name="SingleArches" DisplayAs="Arches" parm1="4" parm2="50" StringType="Single Color Red"/>
    <model name="Head" DisplayAs="DmxMovingHeadAdv" parm1="1" parm2="1"/>
    <model name="Weird" DisplayAs="Frobnicator"/>
    <model name="Lonely" DisplayAs="Single Line" parm1="1" parm2="10" StringType="RGB Nodes" LayoutGroup="Garage"/>
    <model name="apple" DisplayAs="Single Line" parm1="1" parm2="10" StringType="RGB Nodes" LayoutGroup="Garage"/>
  </models>
  <modelGroups>
    <modelGroup name="AllArches" models="Arch1,Arch2,Arch10" LayoutGroup="Front"/>
    <modelGroup name="Yard" models="AllArches,Star,Window,Arch1"/>
    <modelGroup name="Everything" models="Yard,MegaTree/Top,Matrix,Ghost"/>
    <modelGroup name="LoopA" models="LoopB,Head"/>
    <modelGroup name="LoopB" models="LoopA,Weird"/>
  </modelGroups>
  <views>
    <view name="Master View" models="Arch1,Star,Yard,apple"/>
    <view name="Roof" models="Matrix"/>
  </views>
</xrgb>
"""


def test_xlayout_logic():
    print("\n-- xlayout_tab: reading an xLights layout --")
    import xlayout_tab as xl
    path = os.path.join(TMP, "xlights_rgbeffects.xml")
    with open(path, "w") as f:
        f.write(LAYOUT_XML)
    other = os.path.join(TMP, "other.xml")
    with open(other, "w") as f:
        f.write("<?xml version='1.0'?><settings/>")
    check(xl.is_layout_file(path) and not xl.is_layout_file(other) and not xl.is_layout_file(os.path.join(TMP, "x.txt")),
          "only an .xml with an <xrgb> root is taken as a layout")
    lay = xl.parse_layout(path)
    nodes = {n: m["nodes"] for n, m in lay["models"].items()}
    check(len(lay["models"]) == 13 and len(lay["groups"]) == 5, "models and groups are read")
    check(nodes["Arch1"] == 50 and nodes["MegaTree"] == 1600 and nodes["Matrix"] == 1600 and nodes["Star"] == 100,
          "node counts: strings x nodes per string")
    check(nodes["Window"] == 140, "...a Window Frame: top + 2 sides + bottom")
    check(nodes["Custom1"] == 6, "...a Custom model: distinct node numbers in its grid")
    check(nodes["SingleArches"] == 4, "...single-color strings: one node per string")
    check(nodes["Head"] is None and xl.nodes_text(None, "DmxMovingHeadAdv") == ""
          and nodes["Weird"] is None and xl.nodes_text(None, "Frobnicator") == "?",
          "...none for DMX (blank) or an unknown type (?)")
    comp = xl.node_count({"DisplayAs": "Custom", "CustomModelCompressed": "1,0,0;2,0,1;2,1,1;3,1,0"})
    check(comp == 3, "...also the newer compressed Custom format")
    yard = xl.group_models(lay, "Yard")
    check(yard["Star"] == "direct" and yard["Arch1"] == "direct" and yard["Arch2"] == "indirect",
          "a group's own members are direct, members of nested groups indirect (direct wins)")
    ev = xl.group_models(lay, "Everything")
    check(ev["MegaTree"] == "direct" and ev["Arch10"] == "indirect" and ev["Star"] == "indirect",
          "a submodel member (MegaTree/Top) counts as its model; nesting goes any levels deep")
    check(lay["groups"]["Everything"]["unknown"] == ["Ghost"], "members that aren't in the layout are noted")
    both = xl.groups_to_models(lay, ["Everything", "AllArches"])
    check(both["Arch10"] == "direct" and both["Matrix"] == "direct", "with several groups selected, direct in any wins")
    check(set(xl.ungrouped_models(lay)) == {"Custom1", "SingleArches", "Lonely", "apple"}, "models in no group")
    check(xl.groups_to_models(lay, [xl.UNGROUPED]) == {m: "direct" for m in xl.ungrouped_models(lay)},
          "\"(not in any group)\" selects those")
    tops = xl.top_level_groups(lay)
    check(tops[0] == "Everything" and "LoopA" in tops and "Yard" not in tops,
          "top-level groups (a group cycle doesn't lose its groups or hang)")
    check(xl.group_depth(lay) == 3, "nesting depth")
    check(set(xl.group_models(lay, "LoopA")) == {"Head", "Weird"}, "a cycle of groups is followed only once")

    rows = xl.model_rows(lay, {"Star": {"style": "sparkle"}, "Arch1": {"style": "chase", "comment": "left side"}})
    names = [r["model"] for r in xl.sort_rows(rows, "model")]
    check(names.index("Arch2") < names.index("Arch10"), "sorting is natural: Arch2 before Arch10")
    by_nodes = xl.sort_rows(rows, "nodes", reverse=True)
    check(by_nodes[0]["nodes"] == 1600 and by_nodes[-1]["nodes"] is None, "sort by nodes, empty values last")
    check([r["model"] for r in xl.sort_rows(rows, "style")][:2] == ["Arch1", "Star"], "sort by style")
    f = lambda col, spec: sorted(r["model"] for r in xl.filter_rows(rows, col, spec))
    check(f("nodes", ">100") == ["Matrix", "MegaTree", "Window"], "filter Nodes > 100")
    check(f("nodes", "40-60") == ["Arch1", "Arch10", "Arch2"], "filter Nodes by a range")
    check(f("type", "=arches") == ["Arch1", "Arch10", "Arch2", "SingleArches"], "filter Type =exact (any case)")
    check(f("style", "=") == sorted(set(names) - {"Star", "Arch1"}), "\"=\" alone: empty values")
    check(f("type", "!arch") == sorted(set(names) - {"Arch1", "Arch2", "Arch10", "SingleArches"}), "\"!\" excludes")
    check(f(xl.ANY_COLUMN, "left") == ["Arch1"], "Any column searches every column (here the comment)")
    check(f("comment", "") == sorted(names), "an empty filter shows everything")
    text = xl.layout_summary(path, lay, {})
    check("Models: {cyan}13" in text and "Groups: {cyan}5" in text and "Ghost" in text and "Arches" in text,
          "the text panel summary has the model and group counts, types and unknown members")
    return path


def test_xlayout_view(path):
    print("\n-- xlayout_tab: the group tree and model list --")
    import xlayout_tab as xl
    import utils
    import timing_helpers as th
    canvas, text, tab = FakeCanvas(FakeWidget()), FakeText(), FakeTab()
    check(xl.onload(path, canvas=canvas, text=text, tab=tab), "the plugin claims the layout file")
    view = canvas._layout_view
    check("Models: " in text.get() and tab.protect_file and tab.save_hook == view.save,
          "summary in the text panel; the layout file itself is protected")
    check(tab.title_detail == "13 models, 5 groups", "window title detail")
    gt, mt = view.group_tree, view.model_tree
    top_names = [view._group_iids[i] for i in gt.get_children()]
    check(top_names[:1] == ["Everything"] and top_names[-1] == xl.UNGROUPED, "the tree starts with the top-level groups")
    ev_iid = gt.get_children()[0]
    child_names = [view._group_iids[i] for i in gt.get_children(ev_iid)]
    check(child_names == ["Yard"] and [view._group_iids[i] for i in gt.get_children(gt.get_children(ev_iid)[0])]
          == ["AllArches"], "nested groups are children in the tree (collapsible)")
    check(len(mt.get_children()) == 13, "with no group selected, all models are listed")
    yard_iid = gt.get_children(ev_iid)[0]
    gt.selection_set((yard_iid,)); view._on_group_select()
    rows = {iid: mt.item(iid) for iid in mt.get_children()}
    check(set(rows) == {"Arch1", "Arch2", "Arch10", "Star", "Window"}, "selecting a group lists its models")
    check(rows["Arch2"]["tags"][0] == "indirect" and rows["Star"]["tags"][0] == "direct"
          and rows["Arch1"]["tags"][0] == "direct", "...models only in a nested group are tagged indirect (gray)")
    check("via nested groups" in view.count_var.get(), "...and the count says so")
    view.clear_groups()
    check(len(mt.get_children()) == 13 and gt.selection() == (), "Clear shows all models again")

    view.sort_by("nodes")
    first = mt.get_children()[0]
    check(mt.item(first)["values"][2] in ("4", "6"), "clicking the Nodes heading sorts by nodes")
    view.sort_by("nodes")
    check(mt.item(mt.get_children()[0])["values"][2] == "1,600" and "\u25bc" in mt.headings["nodes"]["text"],
          "...again: reversed, with the arrow in the heading")
    check(mt.headings["model"]["text"] == "Model", "only the sorted column shows an arrow")
    view.set_filter("type", "=arches")
    check(len(mt.get_children()) == 4 and view.filter_column.get() == "Type", "filter by a column")
    view.clear_filter()

    ed = view.begin_edit("Star", "style")
    ed_var = view._editor["var"]
    ed_var.set("sparkle")
    view.end_edit(commit=True)
    check(view.notes["Star"] == {"style": "sparkle"} and tab.dirty, "editing a Style cell sets it (tab unsaved)")
    check(mt.item("Star")["values"][xl.COLUMNS.index("style")] == "sparkle", "...and the list shows it")
    view.begin_edit("Star", "comment")
    view._editor["var"].set("  by the door ")
    view.end_edit(commit=True)
    view.begin_edit("Star", "comment")
    view._editor["var"].set("changed my mind")
    view.end_edit(commit=False)
    check(view.notes["Star"]["comment"] == "by the door", "Comment edits too; Esc cancels")
    mt.selection_set(("Arch1", "Arch2"))
    menu = view.build_model_menu("Arch1", "type")
    labels = menu.labels()
    check("Set comment for 2 selected models..." in labels and "Filter: Type = \u201cArches\u201d" in labels,
          "right-click: set for all selected models, or filter by the clicked value")
    styles = next(e for e in menu.entries if e.get("kind") == "cascade")["menu"]
    styles.invoke_label("sparkle")
    check(view.notes["Arch1"]["style"] == "sparkle" and view.notes["Arch2"]["style"] == "sparkle",
          "the style list offers styles already in use, for all selected models at once")
    check("sparkle" in (utils.get_preference("xlayout_styles") or []), "styles are remembered for other layouts too")
    menu.invoke_label("Filter: Type = \u201cArches\u201d")
    check(len(mt.get_children()) == 4, "Filter by value works from the menu")
    view.clear_filter()
    view.undo()
    check("Arch1" not in view.notes, "undo: one step per action (the style for both models)")
    view.redo()
    check(view.notes["Arch2"]["style"] == "sparkle", "redo")
    check(view.save() and th.load_cache(path)["model_notes"]["Star"] == {"style": "sparkle", "comment": "by the door"},
          "notes are saved in the sidecar <stem>-tracked.json")
    check(os.path.basename(th.cache_path(path)) == "xlights_rgbeffects-tracked.json", "...named after the layout file")
    check(open(path).read() == LAYOUT_XML, "the layout file is never written")
    view.set_note(["Star"], "comment", "")
    check("comment" not in view.notes["Star"], "clearing a value removes it")
    canvas2, text2, tab2 = FakeCanvas(FakeWidget()), FakeText(), FakeTab()
    xl.onload(path, canvas=canvas2, text=text2, tab=tab2)
    check(canvas2._layout_view.notes["Arch1"]["style"] == "sparkle", "notes come back when the layout is reopened")
    check("With a style or comment: {cyan}" not in text2.get() and "With a style or comment: " in text2.get(),
          "the summary counts the models with notes")

    utils.clear_tab_plugins_cache()
    names = [m.__name__ for m in utils.discover_tab_plugins()]
    check("xlayout_tab" in names, "the plugin is discovered (xlayout_tab.py matches *_tab.py)")
    check(utils.run_onload_plugins(path, canvas=FakeCanvas(FakeWidget()), text=FakeText(), tab=FakeTab()),
          "opening/dropping the layout file opens it with xlayout_tab")
    other = os.path.join(TMP, "other.xml")
    check(not utils.run_onload_plugins(other, canvas=FakeCanvas(FakeWidget()), text=FakeText(), tab=FakeTab()),
          "an unrelated .xml is still opened as text")
    import tracked
    ft = tracked.open_filetypes()
    labels = [n for n, _p in ft]
    check(ft[0][0] == "Supported files" and ft[-1] == ("All files", "*"), "File > Open: all supported types first")
    check({"Audio", "Images", "Log files", "xLights layout", "Text / lyrics"} <= set(labels),
          "...then one entry per plugin, from each plugin's FILE_TYPES")
    check(all(p in ft[0][1].split() for p in ("*.mp3", "*.MP3", "*.xml", "*.log", "*.png", "*.srt")),
          "...the first entry covers every plugin's types, in both cases (Tk's filter is case-sensitive)")
    fake = types.ModuleType("fake_tab")
    fake.onload = lambda *a, **k: False
    fake.FILE_TYPES = [("Widgets", "*.wdg")]
    real_discover = utils.discover_tab_plugins
    calls = {"n": 0}

    def counting():
        calls["n"] += 1
        return real_discover() + [fake]
    utils.clear_tab_plugins_cache()
    utils.discover_tab_plugins = counting
    try:
        check(("Widgets", "*.wdg *.WDG") in tracked.open_filetypes(), "a new plugin's types show up without touching tracked.py")
        tracked.open_filetypes(); tracked.open_filetypes()
        check(calls["n"] == 1, "the plugins' file types are collected once per session, then reused")
    finally:
        utils.discover_tab_plugins = real_discover
        utils.clear_tab_plugins_cache()
    bad = os.path.join(TMP, "broken.xml")
    with open(bad, "w") as f:
        f.write("<xrgb><models><model name='x'")
    t3 = FakeText()
    check(xl.onload(bad, canvas=FakeCanvas(FakeWidget()), text=t3, tab=FakeTab()) and "Couldn't read" in t3.get(),
          "a broken layout file shows the error instead of failing")


def test_xlayout_round3(path):
    print("\n-- xlayout_tab: previews, Master View, sorting, stripes and borders --")
    import xlayout_tab as xl
    import utils
    import tracked
    lay = xl.parse_layout(path)
    check(lay["models"]["Lonely"]["preview"] == "Garage" and lay["models"]["Arch1"]["preview"] == "Default",
          "each model's preview (LayoutGroup; \"Default\" when unset)")
    check(lay["groups"]["AllArches"]["preview"] == "Front", "...groups have one too")
    check(xl.in_master(lay, "Star") is True and xl.in_master(lay, "Arch2") is False and xl.in_master(lay, "Yard") is True,
          "Master View membership from <view name=\"Master View\">, for models and groups")
    check(lay["views"]["Roof"] == ["Matrix"], "other views are read too")
    other = os.path.join(TMP, "nomaster.xml")
    with open(other, "w") as f:
        f.write('<xrgb><models><model name="A" DisplayAs="Arches" parm1="1" parm2="5"/></models></xrgb>')
    nm = xl.parse_layout(other)
    check(nm["master"] is None and xl.in_master(nm, "A") is None, "no Master View list: membership unknown (not \"no\")")
    check("no <view name=" in xl.layout_summary(other, nm, {}), "...and the summary says so")
    summary = xl.layout_summary(path, lay, {})
    check("Previews:" in summary and "Garage" in summary and "Master View: {cyan}3" in summary,
          "the summary lists the previews and the Master View counts")

    rows = xl.model_rows(lay, {})
    f = lambda col, spec: sorted(r["model"] for r in xl.filter_rows(rows, col, spec))
    check(f("master", "yes") == ["Arch1", "Star", "apple"] and f("master", "\u2713") == f("master", "yes"),
          "filter Master: yes / \u2713")
    check(len(f("master", "no")) == 10 and f("master", "!yes") == f("master", "no"), "...no / !yes")
    check(f("preview", "=garage") == ["Lonely", "apple"], "filter by Preview")
    check(f(xl.ANY_COLUMN, "\u2713") == ["Arch1", "Star", "apple"], "Any column also sees the Master mark")
    by_master = [r["model"] for r in xl.sort_rows(rows, "master")]
    check(set(by_master[:3]) == {"Arch1", "Star", "apple"}, "sort by Master: members first")
    check([r["model"] for r in xl.sort_rows(rows, "preview")][:2] == ["Arch1", "Arch2"],
          "sort by Preview (then by name)")
    names = [r["model"] for r in xl.sort_rows(rows, "model")]
    check(names.index("Weird") < names.index("apple"), "default sort is case-sensitive: \"Weird\" before \"apple\"")
    names_ci = [r["model"] for r in xl.sort_rows(rows, "model", case_sensitive=False)]
    check(names_ci.index("apple") < names_ci.index("Arch1"), "...optionally case-insensitive: \"apple\" first")
    check(names.index("Arch2") < names.index("Arch10"), "numbers still sort by value")
    check(xl.sort_group_names(lay, ["Yard", "LoopA", "Everything"]) == ["Everything", "LoopA", "Yard"],
          "groups sort alphabetically by default")
    check(xl.sort_group_names(lay, ["Yard", "AllArches", "LoopA"], "count", reverse=True)[0] == "Yard",
          "...or by their model count")
    check(xl.sort_group_names(lay, ["LoopA", "Yard", "AllArches"], "master") == ["Yard", "AllArches", "LoopA"],
          "...or by Master View membership")
    xs, ys = xl.grid_positions([(0, 30, 100, 20), (100, 30, 60, 20)], 100)
    check(xs == [99, 159] and ys == [29, 49, 69, 89], "cell borders: column right edges, one line per row")
    check(xl.grid_positions([], 100) == ([], []), "...none without rows")

    canvas, text, tab = FakeCanvas(FakeWidget()), FakeText(), FakeTab()
    xl.onload(path, canvas=canvas, text=text, tab=tab)
    view = canvas._layout_view
    gt, mt = view.group_tree, view.model_tree
    tops = [view._group_iids[i] for i in gt.get_children()]
    check(tops == ["Everything", "LoopA", "LoopB", xl.UNGROUPED], "the group tree is sorted alphabetically, (not in any group) last")
    ev = gt.get_children()[0]
    gt.items[ev]["open"] = True
    yard = gt.get_children(ev)[0]
    gt.selection_set((yard,)); view._on_group_select()
    view.sort_groups("group")
    check([view._group_iids[i] for i in gt.get_children()][:3] == ["LoopB", "LoopA", "Everything"]
          and "\u25bc" in gt.headings["#0"]["text"], "clicking the Groups heading again reverses the order")
    new_ev = next(i for i in gt.get_children() if view._group_iids[i] == "Everything")
    check(gt.item(new_ev, "open") and [view._group_iids[i] for i in gt.selection()] == ["Yard"],
          "...keeping expanded groups and the selection")
    view.sort_groups("count")
    check(gt.headings["count"]["text"].endswith("\u25b2") and gt.headings["#0"]["text"] == "Groups",
          "the Models heading sorts too (only the sorted column shows an arrow)")
    row_values = gt.item(new_ev)["values"]
    check(len(row_values) == 3, "the group tree shows Models, Preview and Master")
    shown = [i for i in gt.get_children()] + list(gt.get_children(new_ev))
    tags = [gt.item(i)["tags"][0] for i in sorted(shown, key=lambda i: 0)]
    check(all(t in ("even", "odd") for t in tags), "group rows alternate colors")
    view.clear_groups()
    mtags = [mt.item(i)["tags"][1] for i in mt.get_children()]
    check(mtags[:4] == ["even", "odd", "even", "odd"], "model rows alternate colors")
    star = mt.item("Star")["values"]
    check(star[xl.COLUMNS.index("master")] == "\u2713" and star[xl.COLUMNS.index("preview")] == "Default",
          "the model list shows Preview and the Master mark")
    view.set_filter("master", "yes")
    check(len(mt.get_children()) == 3, "filter the list by Master")
    view.clear_filter()
    first_before = mt.get_children()[0]

    class App:
        tabs = [types.SimpleNamespace(canvas=canvas)]
    utils.set_preference(tracked.PREF_LAYOUT_SORT_CASE, True)
    tracked.EditorApp.set_layout_sort_case(App(), False)
    check(utils.get_preference(xl.PREF_SORT_CASE) is False and mt.get_children()[0] == "apple",
          "Preferences: turning case-sensitive sorting off re-sorts open layouts right away")
    tracked.EditorApp.set_layout_sort_case(App(), True)
    check(mt.get_children()[0] == first_before, "...and on again (the default)")


def test_logview_wrap():
    print("\n-- log viewer: one wrap button (none / word / hard) --")
    import logview_tab as lv
    check(lv.wrap_mode_from_pref(True) == "word" and lv.wrap_mode_from_pref(False) == "none"
          and lv.wrap_mode_from_pref("char") == "char", "the old on/off setting still loads")
    text, tab = FakeText(), FakeTab()
    state = lv._LogViewState(tab, os.path.join(TMP, "x.log"))
    lv._set_pref(lv.PREF_WRAP, "char")
    lv._build_controls(FakeCanvas(FakeWidget()), text, tab, state)
    check(text.cget("wrap") == "char" and state.wrap_button.cget("text") == "Hard wrap \u25be",
          "the saved mode is applied, and shown on the button")
    radios = [e for e in state.wrap_menu.entries if e.get("kind") == "radio"]
    check([e["value"] for e in radios] == ["none", "word", "char"], "its menu offers no wrap, word wrap, hard wrap")
    state.wrap_var.set("word"); radios[1]["command"]()
    check(text.cget("wrap") == "word" and lv._get_pref(lv.PREF_WRAP, None) == "word"
          and state.wrap_button.cget("text") == "Word wrap \u25be", "choosing one applies and remembers it")
    state.wrap_var.set("none"); radios[0]["command"]()
    check(text.cget("wrap") == "none", "no wrap")
    import editor_tab
    src = open(editor_tab.__file__).read()
    check('debug(11, f"{{blue}}Restored sash' in src and 'debug(11, f"{{blue}}Restored cursor' in src,
          "the sash/cursor restore messages moved to debug level 11 (hidden at the default 10)")


def test_round4(th, wt, media, layout_path):
    print("\n-- xlayout: a model's groups highlighted; cards: End moves the later marks --")
    import xlayout_tab as xl
    lay = xl.parse_layout(layout_path)
    got = xl.groups_containing(lay, ["Arch2"])
    check(got == {"AllArches": "direct", "Yard": "indirect", "Everything": "indirect"},
          "groups_containing: direct membership and through nested groups")
    check(xl.groups_containing(lay, ["Arch1"])["Yard"] == "direct", "...direct wins (Arch1 is also Yard's own member)")
    check(xl.groups_containing(lay, ["Lonely"]) == {} and xl.groups_containing(lay, []) == {}, "...none for a loose model")
    canvas, text, tab = FakeCanvas(FakeWidget()), FakeText(), FakeTab()
    xl.onload(layout_path, canvas=canvas, text=text, tab=tab)
    view = canvas._layout_view
    gt, mt = view.group_tree, view.model_tree
    mt.selection_set(("Arch2",))
    mt.fire("<<TreeviewSelect>>")
    tagged = {view._group_iids[i]: gt.item(i)["tags"] for i in view._group_iids if gt.item(i)["tags"][0].startswith("hl_")}
    check(tagged.get("AllArches") == ("hl_direct",) and tagged.get("Yard") == ("hl_indirect",)
          and tagged.get("Everything") == ("hl_indirect",), "clicking a model highlights its groups (direct / indirect)")
    check(set(tagged) == {"AllArches", "Yard", "Everything"}, "...and only those")
    aa = next(i for i, n in view._group_iids.items() if n == "AllArches")
    parent = gt.parent(aa)
    check(parent and gt.item(parent, "open") and gt.item(gt.parent(parent), "open"),
          "...opening the tree down to them")
    check(getattr(gt, "seen", None) == next(i for i, n in view._group_iids.items() if n == "Everything"),
          "...and scrolling the first one into view")
    check(len(mt.get_children()) == 13, "highlighting doesn't filter anything")
    view.sort_groups("count")
    check(any(gt.item(i)["tags"] == ("hl_direct",) for i in gt.get_children(parent) or ()) or
          any(gt.item(i)["tags"] == ("hl_direct",) for i in view._group_iids), "the highlight survives re-sorting the groups")
    mt.selection_set(()); mt.fire("<<TreeviewSelect>>")
    check(not any(gt.item(i)["tags"][0].startswith("hl_") for i in view._group_iids),
          "no model selected: no highlight (normal stripes)")

    path = fresh_copy(media, "shiftrest")
    ctl, *_ = bare_controller(wt, path)
    tr = ctl._new_track("Words")
    a = ctl._add_mark("range", 1.0, 2.0, label="a", track_id=tr["id"])
    b = ctl._add_mark("range", 2.5, 3.0, label="b", track_id=tr["id"])
    c = ctl._add_mark("point", 4.0, None, label="c", track_id=tr["id"])
    other = ctl._new_track("Other")
    o = ctl._add_mark("range", 5.0, 6.0, label="o", track_id=other["id"])
    panel = ctl.panel
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    check("rest" in panel.cards[a["id"]] and panel.cards[a["id"]]["rest"].cget("text") == "Join> none",
          "each card has the rest button next to End (off at first)")
    panel.step_var.set("0.25")
    panel._nudge(a["id"], "end", 1)
    check(abs(a["end"] - 2.25) < 1e-9 and abs(b["start"] - 2.5) < 1e-9, "rest off: End + moves only this card")
    panel._cycle_rest()
    check(panel.rest_mode == "group" and all(c["rest"].cget("text") == "Join> group" for c in panel.cards.values()),
          "click: Join>: group (shown on every card)")
    panel._cycle_rest()
    check(panel.rest_mode == "all" and all(c["rest"].cget("text") == "Join> all" for c in panel.cards.values()),
          "click again: Join>: all")
    before = len(ctl._mark_history)
    panel._nudge(a["id"], "end", 1)
    check(abs(a["end"] - 2.5) < 1e-9 and abs(b["start"] - 2.75) < 1e-9 and abs(b["end"] - 3.25) < 1e-9
          and abs(c["start"] - 4.25) < 1e-9, "rest: all -- End changes and every later mark moves the same amount")
    check(o["start"] == 5.0, "...other tracks don't move")
    check(len(ctl._mark_history) == before + 1, "...all in one undo step")
    panel._nudge(a["id"], "end", -1)
    check(abs(a["end"] - 2.25) < 1e-9 and abs(b["start"] - 2.5) < 1e-9, "End \u2212 pulls them back")
    panel._nudge(b["id"], "end", 1)
    check(abs(a["end"] - 2.25) < 1e-9 and abs(c["start"] - 4.25) < 1e-9, "earlier marks never move")
    card = panel.cards[a["id"]]
    card["end"].delete(0, "end"); card["end"].insert(0, "0:02.000")
    panel._commit_time(a["id"], "end")
    check(abs(a["end"] - 2.0) < 1e-9 and abs(b["start"] - 2.25) < 1e-9, "typing an End moves them too")
    ctl.undo_marks()
    a, b, c = ctl.mark_by_id(a["id"]), ctl.mark_by_id(b["id"]), ctl.mark_by_id(c["id"])     # undo restores copies
    check(abs(a["end"] - 2.25) < 1e-9 and abs(b["start"] - 2.5) < 1e-9, "undo restores all of them")
    check(not ctl.set_mark_end_shifting(a["id"], a["start"]), "an End at/before Start is refused (nothing moves)")

    # the reported bug: with a mark already ending at the end of the audio,
    # rest used to stop End from changing at all
    dur = ctl.audio_duration
    z = ctl._add_mark("range", dur - 1.0, dur, label="last", track_id=tr["id"])
    old_end = a["end"]
    panel._nudge(a["id"], "end", 1)
    a, z = ctl.mark_by_id(a["id"]), ctl.mark_by_id(z["id"])
    check(abs(a["end"] - (old_end + 0.25)) < 1e-9, "rest: all with a mark already at the end of the audio: End still changes")
    check(abs(z["end"] - (dur + 0.25)) < 1e-9 and abs(z["start"] - (dur - 0.75)) < 1e-9,
          "...the last mark moves past the end of the audio, keeping its length")
    ctl.undo_marks()
    a, z = ctl.mark_by_id(a["id"]), ctl.mark_by_id(z["id"])
    check(ctl.set_mark_end_shifting(a["id"], a["end"] + 0.2 * dur), "a move of 20% of the audio...")
    z = ctl.mark_by_id(z["id"])
    check(abs(z["end"] - 1.1 * dur) < 1e-9 and z["end"] - z["start"] >= th.MIN_RANGE - 1e-9,
          "...squeezes the last mark against 10% past the end")
    ctl.undo_marks()
    ctl.delete_mark_by_id(z["id"])

    # rest: to gap
    panel.set_rest_mode("group")
    tr2 = ctl._new_track("Chain")
    p1 = ctl._add_mark("range", 1.0, 2.0, label="p1", track_id=tr2["id"])
    p2 = ctl._add_mark("range", 2.0, 3.0, label="p2", track_id=tr2["id"])
    p3 = ctl._add_mark("range", 3.0, 3.5, label="p3", track_id=tr2["id"])
    p4 = ctl._add_mark("range", 4.0, 5.0, label="p4", track_id=tr2["id"])
    check([m["id"] for m in ctl.rest_followers(p1["id"], "group")] == [p2["id"], p3["id"]],
          "to gap: the followers are the marks that touch, up to the first gap")
    check(ctl.set_mark_end_shifting(p1["id"], 2.25, mode="group"), "End +0.25 ...")
    p1, p2, p3, p4 = (ctl.mark_by_id(m["id"]) for m in (p1, p2, p3, p4))
    check(abs(p2["start"] - 2.25) < 1e-9 and abs(p3["end"] - 3.75) < 1e-9 and p4["start"] == 4.0,
          "...moves that block; the mark after the gap stays")
    ctl.set_mark_end_shifting(p1["id"], 3.0, mode="group")
    p1, p3, p4 = (ctl.mark_by_id(m["id"]) for m in (p1, p3, p4))
    check(abs(p3["end"] - 4.0) < 1e-9 and abs(p1["end"] - 2.5) < 1e-9 and p4["start"] == 4.0,
          "...and stops where the block touches the next mark")
    ctl.set_mark_end_shifting(p1["id"], 2.75, mode="group")
    p4 = ctl.mark_by_id(p4["id"])
    check(abs(p4["start"] - 4.25) < 1e-9, "...a further step carries that mark along too")
    panel.set_rest_mode("all"); panel._cycle_rest()
    check(panel.rest_mode == "off", "a third click turns it off")




def make_notes_wav(name, notes, seconds=5.0, rate=22050):
    """A mono WAV: silence with sine notes [(start, end, amplitude)]."""
    import wave, struct, math
    path = os.path.join(TMP, name + ".wav")
    frames = bytearray()
    for i in range(int(seconds * rate)):
        t = i / rate
        v = 0.0
        for s0, s1, amp in notes:
            if s0 <= t < s1:
                v = amp * math.sin(2 * math.pi * 440 * t)
        frames += struct.pack("<h", int(max(-1.0, min(1.0, v)) * 32000))
    with wave.open(path, "wb") as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(rate)
        w.writeframes(bytes(frames))
    return path


def test_audio_edges(th, wt):
    print("\n-- aligning Start / End to rising / falling edges in the audio --")
    b = 0.005
    env = []
    for i in range(int(3 / b)):
        t = i * b
        v = 0.002
        if 1.0 <= t < 1.5:
            v = 0.5 * min(1.0, (t - 1.0) / 0.03)
        elif 1.5 <= t < 1.56:
            v = 0.5 * (1 - (t - 1.5) / 0.06)
        elif 2.0 <= t < 2.6:
            v = 0.4
        env.append(v)
    env = th.edge_envelope([(-v, v) for v in env])
    check(abs(th.find_edge(env, 0.0, b, 0.5, "rise") - 1.0) <= 0.015, "find_edge: the foot of the next rising edge")
    check(abs(th.find_edge(env, 0.0, b, 1.0, "rise") - 2.0) <= 0.015,
          "...from on an edge, the next one (so repeated clicks step forward)")
    check(abs(th.find_edge(env, 0.0, b, 1.2, "fall") - 1.56) <= 0.015, "...the bottom of the next falling edge")
    check(abs(th.find_edge(env, 0.0, b, 1.6, "fall") - 2.6) <= 0.02, "...and the one after that")
    check(th.find_edge(env, 0.0, b, 2.7, "rise") is None, "...none past the last one")
    check(th.find_edge([0.2] * 100, 0.0, b, 0.0, "rise") is None, "a flat stretch has no edges")

    path = make_notes_wav("notes", [(1.0, 1.5, 0.8), (2.5, 3.2, 0.4)])
    ctl, *_ = open_controller(wt, path)
    check(ctl.audio_duration and abs(ctl.audio_duration - 5.0) < 0.05, "a test file with two notes")
    t = ctl.edge_time(0.2, "rise")
    check(t is not None and abs(t - 1.0) <= 0.03, f"edge_time rise from 0.2 s -> {t}")
    t = ctl.edge_time(1.0, "rise")
    check(t is not None and abs(t - 2.5) <= 0.03, f"...from 1.0 s the next note: {t}")
    t = ctl.edge_time(1.1, "fall")
    check(t is not None and abs(t - 1.5) <= 0.04, f"edge_time fall from 1.1 s -> {t}")
    check(ctl.edge_time(3.5, "rise") is None, "...none after the last note")
    tr = ctl._new_track("Notes")
    m = ctl._add_mark("range", 0.8, 1.2, label="note", track_id=tr["id"])
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    panel = ctl.panel
    check("start_edge" in panel.cards[m["id"]] and "end_edge" in panel.cards[m["id"]],
          "cards have the \u2197 (Start) and \u2198 (End) buttons")
    panel._snap_edge(m["id"], "start")
    panel._snap_edge(m["id"], "end")
    m = ctl.mark_by_id(m["id"])
    check(abs(m["start"] - (1.0 - 0.15)) <= 0.03 and abs(m["end"] - 1.5) <= 0.04,
          f"\u2197/\u2198 align the card to the note (Start 0.15 s before the edge): {m['start']:.3f}-{m['end']:.3f}")
    n = ctl._add_mark("range", 2.0, 2.2, label="later", track_id=tr["id"])
    panel.set_rest_mode("all")
    panel._snap_edge(m["id"], "end")
    m, n = ctl.mark_by_id(m["id"]), ctl.mark_by_id(n["id"])
    check(abs(m["end"] - 3.2) <= 0.04 and abs((n["start"] - 2.0) - (m["end"] - 1.5)) < 0.05,
          "\u2198 again: the next falling edge; with rest on, later marks move along")
    panel.set_rest_mode("off")
    real = ctl.edge_source
    seen = {}
    ctl.edge_source = lambda use_vocals=True: seen.update(v=use_vocals) or real(use_vocals)
    panel._snap_edge(m["id"], "start")
    check(seen.get("v") is True, "a plain click looks in the vocals stem")
    panel.cards[m["id"]]["start_edge"].fire("<ButtonRelease-1>", Event(state=0x0001))
    panel._snap_edge(m["id"], "start")
    check(seen.get("v") is False, "Shift+click looks in the full mix")
    check(ctl.edge_source(True) == path, "...(the file itself when there are no current stems)")
    ctl.edge_source = real


def test_round6(th, wt, media):
    import timing_panel as tp_mod
    print("\n-- previous edges, 10% past the end, reveal, loop edits, drag, play highlight, pending edits, restore --")
    # previous edges (pure)
    b = 0.005
    env = [0.002] * int(3 / b)
    for i in range(len(env)):
        t = i * b
        if 1.0 <= t < 1.5 or 2.0 <= t < 2.6:
            env[i] = 0.5
    env = th.edge_envelope([(-v, v) for v in env])
    check(abs(th.find_prev_edge(env, 0.0, b, 2.5, "rise") - 2.0) <= 0.015, "find_prev_edge: the previous rising edge")
    check(abs(th.find_prev_edge(env, 0.0, b, 2.0, "rise") - 1.0) <= 0.015, "...from on one, the one before")
    check(abs(th.find_prev_edge(env, 0.0, b, 2.9, "fall") - 2.6) <= 0.02, "...the previous falling edge")
    check(th.find_prev_edge(env, 0.0, b, 0.9, "rise") is None, "...none before the first")
    notes = os.path.join(TMP, "notes.wav")
    ctl, *_ = open_controller(wt, notes)
    t = ctl.edge_time(2.6, "rise", direction=-1)
    check(t is not None and abs(t - 2.5) <= 0.03, f"edge_time back from 2.6 s: {t}")
    t = ctl.edge_time(2.4, "rise", direction=-1)
    check(t is not None and abs(t - 1.0) <= 0.03, f"...from 2.4 s: {t}")
    tr = ctl._new_track("N")
    m = ctl._add_mark("range", 2.7, 3.0, label="n", track_id=tr["id"])
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    panel = ctl.panel
    check("start_edge_prev" in panel.cards[m["id"]] and "end_edge_prev" in panel.cards[m["id"]],
          "cards have \u2196 (previous rising) and \u2199 (previous falling) buttons too")
    panel._snap_edge(m["id"], "start", -1)
    m = ctl.mark_by_id(m["id"])
    check(abs(m["start"] - (2.5 - 0.15)) <= 0.03, f"\u2196 moves Start back to the previous rising edge (less the lead-in): {m['start']:.3f}")
    panel._snap_edge(m["id"], "end", 1)
    panel._snap_edge(m["id"], "end", -1)
    m = ctl.mark_by_id(m["id"])
    check(abs(m["end"] - 3.2) <= 0.05, f"\u2199 refuses to go before Start (stays at the \u2198 edge): {m['end']:.3f}")

    path = fresh_copy(media, "round6")
    ctl, canvas, text, tab = bare_controller(wt, path)
    panel = ctl.panel
    tr = ctl._new_track("Words")
    a = ctl._add_mark("range", 10.0, 12.0, label="a", track_id=tr["id"])
    b2 = ctl._add_mark("range", 40.0, 70.0, label="long", track_id=tr["id"])
    c = ctl._add_mark("range", 80.0, 82.0, label="c", track_id=tr["id"])
    check(ctl.set_mark_times(c["id"], 105.0, 109.0) and not ctl.set_mark_times(c["id"], 105.0, 111.0),
          "marks may reach 10% past the end of the audio, not further")
    ctl.set_mark_times(c["id"], 80.0, 82.0)

    # reveal on focus
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    ctl.view_start, ctl.view_end = 50.0, 60.0
    ctl.select_mark(a["id"], from_panel=True)
    check(ctl.view_start <= 10.0 and ctl.view_end >= 12.0 and abs((ctl.view_end - ctl.view_start) - 10.0) < 1e-9,
          "a card getting focus scrolls the waveform (same zoom) to show it, start and end")
    ctl.view_start, ctl.view_end = 0.0, 10.0
    ctl.select_mark(b2["id"], from_panel=True)
    check(ctl.view_start <= 40.0 <= ctl.view_end, "a card longer than the view: its start (play position) is shown")
    ctl.view_start, ctl.view_end = 0.0, 10.0
    ctl.select_mark(b2["id"], from_panel=True)
    check(ctl.view_start <= 40.0 <= ctl.view_end, "...also when it was already selected (focus moved back to it)")
    ctl.view_start, ctl.view_end = 5.0, 15.0
    ctl.select_mark(a["id"], from_panel=True)
    check((ctl.view_start, ctl.view_end) == (5.0, 15.0), "already fully visible: the waveform doesn't move")

    # loop edits follow the card
    ctl.play_mark_by_id(a["id"], loop=True)
    check((ctl._play_seg_start, ctl._play_seg_end) == (10.0, 12.0), "looping a card")
    ctl.engine.calls.clear()
    panel._nudge(a["id"], "end", 1)
    check(abs(ctl._play_seg_end - 12.1) < 1e-9 and ctl.engine.calls and ctl.engine.calls[-1][0] >= 10.0,
          "changing the looping card's End changes the loop (playback continues with the new span)")
    ctl.set_mark_times(a["id"], 11.0, 12.1)
    check(ctl._play_seg_start == 11.0 and abs(ctl.engine.calls[-1][0] - 11.0) < 1e-6,
          "...its Start too (a position now outside the span restarts at the new start)")
    ctl.engine.active = False
    ctl._poll_playback()
    check(abs(ctl.engine.calls[-1][0] - 11.0) < 1e-6 and abs(ctl.engine.calls[-1][1] - 1.1) < 1e-6,
          "...and the next repeat plays the new span")
    ctl.stop_play()

    # playing highlight
    ctl.cursor_time = 0.0
    ctl.start_play()
    ctl._update_play_highlight(11.5)
    check(panel.playing_mid == a["id"] and panel.cards[a["id"]]["frame"].cget("bg") == tp_mod.CARD_PLAY_BG,
          "playing from the waveform: the card the playhead is in turns green")
    ctl._update_play_highlight(20.0)
    check(panel.playing_mid is None and panel.cards[a["id"]]["frame"].cget("bg") != tp_mod.CARD_PLAY_BG,
          "...and back when the playhead leaves it")
    ctl._update_play_highlight(45.0)
    check(panel.playing_mid == b2["id"], "...the next card as the playhead enters it")
    ctl.stop_play()
    check(panel.playing_mid is None, "stopping clears it")
    check(ctl.mark_at_playhead(tr["id"], 11.0) == a["id"] and ctl.mark_at_playhead(tr["id"], 30.0) is None,
          "mark_at_playhead: none in a gap")

    # drag snapping
    ctl.view_start, ctl.view_end = 0.0, 100.0
    ctl.render_waveform()
    y = ctl._track_layout()["track_top"] + 5
    x = lambda tt: int((tt - ctl.view_start) / (ctl.view_end - ctl.view_start) * 800)
    ctl._on_waveform_press(Event(x=x(55.0), y=y))
    ctl._on_waveform_drag(Event(x=x(57.0), y=y))
    ctl._on_waveform_release(Event(x=x(57.0), y=y))
    b2 = ctl.mark_by_id(b2["id"])
    check(abs(b2["start"] - 42.0) < 1e-6 and abs(b2["end"] - 72.0) < 1e-6,
          f"dragging a mark in its track moves it by small amounts (fine snapping): {b2['start']}")

    # typing marks the tab unsaved; save applies it
    tab.dirty = False
    card = panel.cards[a["id"]]
    card["text"].delete(0, "end"); card["text"].insert(0, "typed")
    card["text"].fire("<KeyRelease>")
    check(tab.dirty, "typing in a card marks the tab unsaved right away")
    check(ctl.save_marks_now() and th.load_marks(path) and
          next(mm for mm in th.load_marks(path) if mm["id"] == a["id"])["label"] == "typed",
          "saving applies the typed text first")
    card["start"].delete(0, "end"); card["start"].insert(0, "0:1")
    FOCUS["w"] = card["start"]
    ctl.save_marks_now()
    check(ctl.mark_by_id(a["id"])["start"] != 1.0 and panel.has_pending(),
          "a time still being typed (focused) isn't applied by a save")
    FOCUS["w"] = None
    ctl.panel._revert(a["id"])

    # a focused End field follows the -/+ buttons (they don't take the focus)
    card = panel.cards[a["id"]]
    FOCUS["w"] = card["end"]
    old_end = ctl.mark_by_id(a["id"])["end"]
    panel.step_var.set("0.1")
    panel._nudge(a["id"], "end", 1)
    new_end = ctl.mark_by_id(a["id"])["end"]
    check(abs(new_end - old_end - 0.1) < 1e-9 and card["end"].get() == th.format_time_ms(new_end),
          "End has the focus while its + is clicked: the field shows the new time")
    FOCUS["w"] = None
    panel._commit_time(a["id"], "end")          # what leaving the field does
    check(abs(ctl.mark_by_id(a["id"])["end"] - new_end) < 1e-9,
          "...so leaving the field afterwards doesn't put the old time back")
    check(not panel.has_pending(), "...and nothing counts as unsaved typing")
    FOCUS["w"] = card["end"]
    card["end"].delete(0, "end"); card["end"].insert(0, "0:13.5")
    panel._nudge(a["id"], "start", -1)
    check(card["end"].get() == "0:13.5", "a field the user has typed into is still left alone")
    FOCUS["w"] = None
    panel._revert(a["id"])

    # remember / restore the selection: with the saves, not on a timer of its own
    import utils
    orig_autosave = utils.get_preference("autosave_seconds")
    ctl.selected = ("mark", a["id"]); ctl.render_waveform(); ctl.save_marks_now()
    delays = []
    real_after = canvas.after
    canvas.after = lambda ms, fn=None, *args: delays.append(ms) or real_after(ms, fn, *args)
    try:
        utils.set_preference("autosave_seconds", 30)
        ctl.selected = ("mark", b2["id"]); ctl.render_waveform()
        check(30000 in delays and th.load_cache(path).get("selection") != ["mark", b2["id"]],
              "a new selection is saved after the auto-save interval, not right away")
    finally:
        canvas.after = real_after
    run_afters()
    check(th.load_cache(path).get("selection") == ["mark", b2["id"]], "the selected card is remembered in the sidecar")
    utils.set_preference("autosave_seconds", 0)
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    check(th.load_cache(path).get("selection") == ["mark", b2["id"]] and ctl.selection_needs_saving(),
          "auto-save off: a new selection waits for an explicit save")
    ctl.save_marks_now()
    check(th.load_cache(path).get("selection") == ["track", tr["id"]] and not ctl.selection_needs_saving(),
          "...File > Save stores it (with the marks)")
    ctl.selected = ("mark", b2["id"]); ctl.render_waveform(); run_afters()
    ctl.before_close()
    check(th.load_cache(path).get("selection") == ["mark", b2["id"]], "...and so does closing the tab / app")
    ctl2, *_ = open_controller(wt, path)
    check(ctl2.selected == ("mark", b2["id"]) and ctl2.panel.mode == "track",
          "reopening the file selects that card again (its track's cards shown)")
    ctl2.selected = ("track", tr["id"]); ctl2.render_waveform(); ctl2.save_marks_now()
    ctl3, *_ = open_controller(wt, path)
    check(ctl3.selected == ("track", tr["id"]), "...or the track, if a track was selected")
    ctl3.selected = None; ctl3.render_waveform(); ctl3.save_marks_now()
    ctl4, *_ = open_controller(wt, path)
    check(ctl4.selected is None, "...and nothing if nothing was")
    utils.set_preference("autosave_seconds", orig_autosave)


def card_order(panel):
    """The cards' mark ids top to bottom in the card list (test helper)."""
    wins = panel.canvas.windows
    return [mid for mid, c in sorted(panel.cards.items(), key=lambda kv: wins[kv[1]["item"]]["coords"][1])]


def test_view_and_slices(th, wt, media):
    print("\n-- zoom/scroll remembered; long tracks load in slices --")
    import utils
    orig_autosave = utils.get_preference("autosave_seconds")
    utils.set_preference("autosave_seconds", 0)
    path = fresh_copy(media, "round8")
    ctl, canvas, text, tab = open_controller(wt, path)
    tr = ctl._new_track("Words")
    d = ctl.audio_duration
    v1 = (round(0.2 * d, 3), round(0.3 * d, 3))
    far = ctl._add_mark("range", 0.7 * d, 0.72 * d, label="far", track_id=tr["id"])
    ctl.view_start, ctl.view_end = v1
    ctl.selected = ("mark", far["id"]); ctl.render_waveform()
    check(ctl.selection_needs_saving(), "zooming/scrolling counts as something to remember (with auto-save off: at the next save)")
    ctl.save_marks_now()
    check(th.load_cache(path).get("view") == list(v1), "the zoom/scroll is saved in the sidecar with the marks")
    ctl2, *_ = open_controller(wt, path)
    check((ctl2.view_start, ctl2.view_end) == v1, "reopening restores the zoom and scroll position")
    check(ctl2.selected == ("mark", far["id"]), "...and the selection, without scrolling to it")
    ctl2.view_start, ctl2.view_end = 0.0, round(0.1 * d, 3)
    ctl2.render_waveform()
    ctl2.before_close()
    ctl3, *_ = open_controller(wt, path)
    check((ctl3.view_start, ctl3.view_end) == (0.0, round(0.1 * d, 3)), "closing saves it too")
    th.update_cache(path, view=[0.5 * d, 0.4 * d])
    ctl4, *_ = open_controller(wt, path)
    check(ctl4.view_start < ctl4.view_end and ctl4.view_start <= 0.7 * d <= ctl4.view_end,
          "an invalid saved view is ignored (and the selected card is shown instead)")
    utils.set_preference("autosave_seconds", orig_autosave)

    import timing_panel as tp
    big = ctl._new_track("Big")
    for i in range(tp.BUILD_AT_ONCE * 3):
        ctl._add_mark("range", i * 0.5, i * 0.5 + 0.4, label=f"w{i}", track_id=big["id"])
    AFTERS.clear()
    ctl.selected = ("track", big["id"]); ctl.render_waveform()
    panel = ctl.panel
    notes = lambda: " ".join(it.get("text", "") for it in panel.canvas.items if "listnote" in (it.get("tags") or ()))
    check(panel.building and "Loading track ..." in notes() and len(panel.cards) < tp.BUILD_AT_ONCE * 3,
          "a long track shows \"Loading track ...\" and builds its cards in slices")
    run_afters()
    check(not panel.building and len(panel.cards) == tp.BUILD_AT_ONCE * 3 and "Loading track" not in notes(),
          "...until all cards are there (the message goes away)")
    AFTERS.clear()
    ctl.selected = ("track", big["id"]); ctl.panel.sync(force=True)
    ctl.selected = ("track", tr["id"]); ctl.render_waveform()
    run_afters()
    check(panel.track_id == tr["id"] and list(panel.cards) == [far["id"]] and not panel.building,
          "switching tracks while one is loading drops that build")
    few = ctl._new_track("Few")
    ctl._add_mark("range", 1.0, 2.0, label="x", track_id=few["id"])
    AFTERS.clear()
    ctl.selected = ("track", few["id"]); ctl.render_waveform()
    check(len(panel.cards) == 1 and not panel.building, "a short track is built at once, as before")


def test_card_speed(th, wt, media):
    print("\n-- cards: change only what changed (delete / split / reorder / selection) --")
    import timing_panel as tp
    path = fresh_copy(media, "cardspeed")
    ctl, canvas, text, tab = bare_controller(wt, path)
    tr = ctl._new_track("Many")
    n = 60
    ids = [ctl._add_mark("range", i * 1.5, i * 1.5 + 1.0, label=f"w{i}", track_id=tr["id"])["id"] for i in range(n)]
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    panel = ctl.panel
    in_order = lambda: card_order(panel)
    check(len(panel.cards) == n and in_order() == ids, "a 60-card track, cards in time order")
    builds = []
    real_build = panel._build
    panel._build = lambda *a, **k: builds.append(1) or real_build(*a, **k)
    made = []
    real_make = panel._make_card
    panel._make_card = lambda *a, **k: made.append(1) or real_make(*a, **k)
    try:
        panel._delete(ids[30])
        run_afters()
        now = [m["id"] for m in ctl.track_marks(tr["id"])]
        check(not builds and not made and ids[30] not in panel.cards and in_order() == now,
              "deleting a card (\u2715) removes just that card -- no rebuild of the others")
        check(panel.cards[now[30]]["num"].cget("text") == "#31" and panel.cards[now[-1]]["merge"].cget("state") == "disabled",
              "...the cards after it are renumbered")
        ctl.split_mark_by_id(now[10], at_time=15.5)
        run_afters()
        now = [m["id"] for m in ctl.track_marks(tr["id"])]
        check(not builds and len(made) == 1 and in_order() == now, "splitting adds just the new card, in its place")
        ctl.set_mark_times(now[5], 80.0, 80.5)       # past many neighbors
        ctl.render_waveform(); run_afters()
        now = [m["id"] for m in ctl.track_marks(tr["id"])]
        check(not builds and len(made) == 1 and in_order() == now,
              "a time change past its neighbors just moves that card in the list (nothing re-made)")
        ctl._delete_last = None
        panel._delete(now[-1])
        run_afters()
        now = [m["id"] for m in ctl.track_marks(tr["id"])]
        check(panel.cards[now[-1]]["merge"].cget("state") == "disabled"
              and panel.cards[now[-2]]["merge"].cget("state") == "normal", "the new last card gets its Merge \u2193 disabled")
        gone = set(now[:25])
        ctl.marks = [m for m in ctl.marks if m["id"] not in gone]
        ctl.render_waveform(); run_afters()
        check(not builds and in_order() == [m["id"] for m in ctl.track_marks(tr["id"])],
              "even many cards at once are just removed from the list (no rebuild)")
    finally:
        panel._build, panel._make_card = real_build, real_make

    painted = []
    real_paint = panel._paint
    panel._paint = lambda card, bg: painted.append(card) or real_paint(card, bg)
    touched = []
    real_set = panel._set_entry
    panel._set_entry = lambda e, v: touched.append(e) or real_set(e, v)
    try:
        now = [m["id"] for m in ctl.track_marks(tr["id"])]
        ctl.select_mark(now[3])
        run_afters()
        painted.clear(); touched.clear()
        check(panel.select_adjacent_card(1) == "break" and ctl.selected == ("mark", now[4]),
              "Down in the card list selects the next card")
        run_afters()
        check(len(painted) == 2 and len(touched) <= 6, f"...repainting just the two cards involved ({len(painted)})")
        panel.select_adjacent_card(-1)
        check(ctl.selected == ("mark", now[3]), "Up selects the previous card")
        ctl.select_mark(now[0]); panel.select_adjacent_card(-1)
        check(ctl.selected == ("mark", now[0]), "...and stops at the first")
        painted.clear()
        ctl.render_waveform(); run_afters()
        check(not painted, "a redraw with nothing changed touches no card")
    finally:
        panel._paint, panel._set_entry = real_paint, real_set
    check(tp._longest_increasing([5, 1, 2, 9, 3, 4], key=lambda x: x) == [1, 2, 3, 4], "longest increasing run")


def test_round10(th, wt, media):
    print("\n-- round 10: drop-zone click, lead-in, join, parentheses voices, Tab, dirty, status, Ctrl+C --")
    import utils
    import tracked
    path = fresh_copy(media, "round10")
    ctl, canvas, text, tab = bare_controller(wt, path)
    panel = ctl.panel
    tr = ctl._new_track("Lyrics")
    a = ctl._add_mark("range", 10.0, 12.0, label="one two", track_id=tr["id"])
    b = ctl._add_mark("range", 13.0, 15.0, label="three", track_id=tr["id"])
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()

    # #2 the new-track zone: a click moves the @cursor, the track stays selected
    layout = ctl._track_layout()
    y = layout["track_top"] + ctl.TRACK_HEIGHT * len(ctl.tracks) + 5
    ctl._on_waveform_press(Event(x=400, y=y))
    ctl._on_waveform_release(Event(x=400, y=y))
    check(ctl.selected == ("track", tr["id"]) and abs(ctl.cursor_time - 50.0) < 0.5,
          "clicking the new-track zone moves the @cursor and keeps the track selected")

    # #4 lead-in before a rising edge
    seen = []
    real_edge = ctl.edge_time
    ctl.edge_time = lambda t, kind, use_vocals=True, direction=1: seen.append(t) or 20.0
    try:
        utils.set_preference("edge_lead_in", 0.15)
        check(abs(ctl.rise_time(12.0) - 19.85) < 1e-9 and abs(seen[-1] - 12.15) < 1e-9,
              "rising edge: Start goes 0.15 s before it (searching from Start + 0.15, so it steps on)")
        utils.set_preference("edge_lead_in", 0.3)
        check(abs(ctl.rise_time(12.0) - 19.7) < 1e-9, "...the lead-in is a preference")
        utils.set_preference("edge_lead_in", 0.15)
        check(utils.get_edge_lead_in() == 0.15, "(default 0.15 s)")
    finally:
        ctl.edge_time = real_edge

    # #5 card playback ends: scroll back to its start
    ctl.play_mark_by_id(a["id"])
    ctl.view_start, ctl.view_end = 50.0, 60.0
    ctl.engine.active = False
    ctl._poll_playback()
    check(ctl._play_state == "stopped" and ctl.view_start <= 10.0 <= ctl.view_end,
          "when a card's playback ends, the waveform scrolls back to its start")

    # #9 join
    check(panel.cards[b["id"]]["join"].cget("text") == "<Join none", "cards have a <Join button by Start (off)")
    panel._cycle_join()
    check(panel.join_mode == "group" and all(c["join"].cget("text") == "<Join group" for c in panel.cards.values()),
          "click: <Join: group, on every card")
    panel._cycle_join()
    check(panel.join_mode == "all" and panel.cards[b["id"]]["join"].cget("text") == "<Join all",
          "click again: <Join: all")
    panel.step_var.set("0.5")
    panel._nudge(b["id"], "start", -1)
    a, b = ctl.mark_by_id(a["id"]), ctl.mark_by_id(b["id"])
    check(abs(b["start"] - 12.5) < 1e-9 and abs(a["end"] - 12.5) < 1e-9,
          "with join on, Start changes also end the previous card right there")
    ctl.undo_marks()
    a, b = ctl.mark_by_id(a["id"]), ctl.mark_by_id(b["id"])
    check(a["end"] == 12.0 and b["start"] == 13.0, "...one undo step")
    check(not ctl.set_mark_start_joined(b["id"], 10.001), "...refused if the previous card would get too short")
    panel.set_join_mode("group")
    panel._nudge(b["id"], "start", -1)
    a, b = ctl.mark_by_id(a["id"]), ctl.mark_by_id(b["id"])
    check(abs(b["start"] - 12.5) < 1e-9 and a["end"] == 12.0,
          "<Join: group -- cards that weren't touching: the previous one stays")
    panel._nudge(b["id"], "start", -1)
    a, b = ctl.mark_by_id(a["id"]), ctl.mark_by_id(b["id"])
    check(abs(b["start"] - 12.0) < 1e-9 and a["end"] == 12.0, "...(now touching: 12.0)")
    panel._nudge(b["id"], "start", -1)
    a, b = ctl.mark_by_id(a["id"]), ctl.mark_by_id(b["id"])
    check(abs(b["start"] - 11.5) < 1e-9 and abs(a["end"] - 11.5) < 1e-9, "...touching cards: the previous one follows")
    ctl.undo_marks(); ctl.undo_marks(); ctl.undo_marks()
    a, b = ctl.mark_by_id(a["id"]), ctl.mark_by_id(b["id"])
    panel.set_join_mode("all"); panel._cycle_join()
    check(panel.join_mode == "off", "a third click: off")

    # #10 parentheses -> the next voice
    c = ctl._add_mark("range", 20.0, 24.0, label="I love you (love you) so", track_id=tr["id"])
    ctl.split_mark_into(c["id"], th.word_spans(c["label"]))
    words = {m["label"]: m for m in ctl.track_marks(tr["id"]) if 20.0 <= m["start"] < 24.0}
    check(words["(love"].get("voices") == ["voice 2"] and words["you)"].get("voices") == ["voice 2"]
          and not words["I"].get("voices") and not words["so"].get("voices"),
          "splitting: words in parentheses get \"voice 2\" (lead = voice 1), the rest keep the card's voices")
    check("voice 2" in ctl.voices, "...the voice is created as needed")
    d = ctl._add_mark("range", 30.0, 34.0, label="hey (ooh ooh)", track_id=tr["id"])
    ctl.set_mark_voices(d["id"], ["voice 2"])
    ctl.split_mark_by_id(d["id"], at_time=31.0)
    parts = [m for m in ctl.track_marks(tr["id"]) if 30.0 <= m["start"] < 34.0]
    check(parts[0].get("voices") == ["voice 2"] and parts[-1].get("voices") == ["voice 3"],
          "Split at cursor too; a card of voice 2 puts its parentheses in voice 3")
    e = ctl._add_mark("range", 40.0, 41.0, label="x", track_id=tr["id"])
    ctl.set_mark_label(e["id"], "(ahh)")
    check(ctl.mark_voices(e["id"]) == ["voice 2"], "a card typed as all-parentheses (no voice yet) gets voice 2")
    ctl.set_mark_label(e["id"], "plain")
    check(ctl.mark_voices(e["id"]) == ["voice 2"], "...(changing the text later doesn't take it away)")
    check(th.in_parentheses("a (b c) d", (3, 4)) and not th.in_parentheses("a (b c) d", (0, 1))
          and th.in_parentheses("a (b c) d", (2, 7)), "in_parentheses")

    # #12 Tab / Shift+Tab
    ctl.render_waveform(); run_afters()
    order = panel.order
    first, second = panel.cards[order[0]], panel.cards[order[1]]
    FOCUS["w"] = None
    check(first["start"].fire("<Tab>") == "break" and FOCUS["w"] is second["start"],
          "Tab in Start: the next card's Start")
    check(second["start"].fire("<Shift-Tab>") == "break" and FOCUS["w"] is first["start"],
          "Shift+Tab: back to the previous card's Start")
    first["text"].fire("<Tab>")
    check(FOCUS["w"] is second["text"].widget or FOCUS["w"] is second["text"],
          "...in the text field: the next card's text field")
    FOCUS["w"] = None

    # #7 dirty on any change, even after an auto-save
    tab.dirty = False
    t0 = panel.cards[order[0]]["text"]
    t0.fire("<FocusIn>")
    t0.insert("end", "!")
    t0.fire("<KeyRelease>")
    check(tab.dirty, "typing marks the tab unsaved")
    ctl.save_marks_now(); tab.dirty = False                     # an auto-save applies it
    FOCUS["w"] = t0
    t0.insert("end", "?")
    t0.fire("<KeyRelease>")
    check(tab.dirty, "...and again after an auto-save, when more is typed")
    FOCUS["w"] = None

    # #8 "Auto-saved ..." goes away once there's something new to save
    status = FakeWidget()
    status.configure(text="Auto-saved song.mp3")
    app = types.SimpleNamespace(status=status, _update_title=lambda: None)
    tracked.EditorApp._on_tab_modified(app, types.SimpleNamespace(dirty=True))
    check(status.cget("text") == "", "the \"Auto-saved\" status is cleared when a tab gets unsaved changes")
    status.configure(text="Opened x")
    tracked.EditorApp._on_tab_modified(app, types.SimpleNamespace(dirty=True))
    check(status.cget("text") == "Opened x", "...other messages stay")

    # #11 gutter refreshes are coalesced
    AFTERS.clear()
    for _ in range(50):
        panel._refresh_gutter(delay_ms=10)
    check(len(AFTERS) <= 1, f"50 scroll steps -> one gutter refresh ({len(AFTERS)})")
    run_afters()

    # #15 Ctrl+C
    calls = []
    fake_app = types.SimpleNamespace(after=lambda ms, fn=None: calls.append(fn), on_quit="quit")
    guard = tracked.InterruptGuard.__new__(tracked.InterruptGuard)
    guard.app, guard.count = fake_app, 1
    import threading
    guard._lock = threading.Lock()
    guard._on_sigint(2, None)
    check(calls == ["quit"], "first Ctrl+C: the normal close (asks about unsaved changes)")
    guard.reset()
    check(guard.count == 0, "Cancel in that question: a later Ctrl+C asks again")
    src = open(tracked.__file__).read()
    check("os._exit(130)" in src and "set_wakeup_fd" in src and "dump_traceback(" in src,
          "second Ctrl+C exits at once (even if the GUI is stuck); a stalled loop prints where it's stuck")


def test_round11(th, wt, media):
    print("\n-- round 11: layout, dark cards, voice text, modifier hints, look-ahead, insert rows, prewarm, teardown --")
    import timing_panel as tp
    import utils
    import tracked
    path = fresh_copy(media, "round11")
    ctl, canvas, text, tab = bare_controller(wt, path)
    panel = ctl.panel
    tr = ctl._new_track("Lyrics")
    ids = [ctl._add_mark("range", i * 2.0, i * 2.0 + 1.5, label=f"w{i}", track_id=tr["id"])["id"] for i in range(8)]
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    card = panel.cards[ids[0]]
    order = [b.cget("text") for b in card["tbtns"]]
    check(order == ["\u2196", "[", "\u21e4", "\u2212", "+", "\u2197", "@", "\u2199", "\u2212", "+", "\u21e5", "]", "\u2198", "@"],
          "Start/End buttons: the earlier ones left of the box, the later ones and @ right of it")
    check(card["join"].cget("text") == "<Join none" and card["rest"].cget("text") == "Join> none",
          "the buttons are named <Join (Start side) and Join> (End side)")
    check(card["frame"].cget("bg") != "#f4f4f4" and tp.contrast_fg(card["frame"].cget("bg")) == tp.LIGHT_TEXT
          and card["start"].cget("bg") == tp.ENTRY_BG, "cards are dark (light text), like the panel around them")

    # #5 voice button
    check(tp.voice_button_text([], "hello") == "Voice \u25be", "no voice: plain Voice button")
    check(tp.voice_button_text([], "(ooh ooh)") == "voice 2 \u25be", "all in parentheses: the implied voice 2")
    check(tp.voice_button_text([], "love (you)") == "voice 1+ \u25be", "mixed: \"+\" after the (implied) voice")
    check(tp.voice_button_text(["Lead"], "love (you)") == "Lead+ \u25be", "...after an assigned voice too")
    check(tp.voice_button_text(["voice 3"], "plain") == "voice 3 \u25be", "assigned voice shown")
    ctl.set_mark_label(ids[1], "go (go)")
    ctl.render_waveform(); run_afters()
    check(panel.cards[ids[1]]["voice"].cget("text") == "voice 1+ \u25be", "...on the card")

    # #9 a card inserted between two others gets its own row
    ctl.split_mark_by_id(ids[2], at_time=4.75)
    run_afters()
    ys = [panel.canvas.windows[panel.cards[mid]["item"]]["coords"][1] for mid in card_order(panel)]
    check(len(ys) == 9 and all(b > a for a, b in zip(ys, ys[1:]))
          and card_order(panel) == [m["id"] for m in ctl.track_marks(tr["id"])],
          "after Split at cursor every card has its own row, in time order")

    # #10 Shift hints
    edge = card["start_edge"]
    normal = edge.cget("fg")
    utils._set_mod("shift", True)
    check(edge.cget("fg") == utils.MOD_HINT_COLORS["shift"] and card["play"].cget("fg") == utils.MOD_HINT_COLORS["shift"],
          "holding Shift: buttons whose Shift+click differs turn amber")
    check(card["start"].cget("fg") == tp.FG and card["delete"].cget("fg") == tp.DELETE_FG, "...others don't")
    utils._set_mod("shift", False)
    check(edge.cget("fg") == normal, "...and back when it's released")
    stems_ok = any(b is ctl.stems_btn for b, _m in utils._mod_buttons) and any(b is ctl.mood_btn for b, _m in utils._mod_buttons)
    check(stems_ok, "the toolbar's Play, Stems and Mood buttons too")

    # #4 look-ahead while playing
    seen = []
    real_see = panel._see
    panel._see = lambda mid: seen.append(mid)
    try:
        ctl.start_play()
        ctl._update_play_highlight(0.5)
        now = panel.order
        check(seen[:2] == [now[2], now[0]],
              "while playing, the cards two ahead are scrolled into view too (the current one stays)")
        ctl.stop_play()
    finally:
        panel._see = real_see

    # #2 prewarm
    check(not hasattr(panel, "_prewarm"), "no prewarm of the cards' windows (it set off the Tk stalls)")

    # #8 no line numbers while cards are shown
    check(tab._line_numbers_shown is False, "line numbers hidden while cards are shown")

    # #11 teardown
    ctl.teardown()
    check(panel.cards == {} and panel.mode == "closing" and panel.list is None,
          "closing: the card list (and every card in it) is dropped in one go")
    before = len(canvas.items)
    ctl.render_waveform()
    check(len(canvas.items) == before, "...and nothing redraws after that")
    calls = []
    fake_tab = types.SimpleNamespace(teardown_hook=lambda: calls.append("tab"), filepath=path)
    app = types.SimpleNamespace(tabs=[fake_tab], withdraw=lambda: calls.append("withdraw"),
                                destroy=lambda: calls.append("destroy"))
    tracked.EditorApp._teardown_and_destroy(app)
    check(calls == ["withdraw", "tab", "destroy"], "quitting: hide the window, let plugins drop their widgets, then destroy")


def test_waveform_mod_hints(th, wt, media):
    print("\n-- Shift / Ctrl hints in the waveform area --")
    import utils
    path = fresh_copy(media, "modhints")
    ctl, canvas, text, tab = bare_controller(wt, path)
    ctl.render_waveform()
    amber, blue = utils.MOD_HINT_COLORS["shift"], utils.MOD_HINT_COLORS["control"]
    back, fwd = ctl.play_back_btn, ctl.play_fwd_btn
    normal = back.cget("fg")
    utils._set_mod("shift", True)
    check(back.cget("fg") == amber and fwd.cget("fg") == amber and ctl.play_btn.cget("fg") == amber
          and ctl.stems_btn.cget("fg") == amber and ctl.mood_btn.cget("fg") == amber,
          "Shift held: \u25c0\u25c0 \u25b6\u25b6 Play Stems Mood turn amber")
    check(ctl.zoom_fit_btn.cget("fg") != amber, "...buttons without a Shift action don't")
    hints = [it for it in canvas.items if "modhint" in (it.get("tags") or ()) and it["kind"] == "text"]
    check(hints and hints[0]["text"].startswith("Shift:") and hints[0]["fill"] == amber,
          "...and the waveform shows what Shift does there")
    utils._set_mod("control", True)
    check(back.cget("fg") == blue and fwd.cget("fg") == blue and ctl.play_btn.cget("fg") == amber,
          "Ctrl held too: \u25c0\u25c0 / \u25b6\u25b6 turn blue (Ctrl wins, as in skip_play); Play stays Shift-amber")
    hints = [it for it in canvas.items if "modhint" in (it.get("tags") or ()) and it["kind"] == "text"]
    check(hints and hints[0]["text"].startswith("Ctrl:") and hints[0]["fill"] == blue, "...the hint says what Ctrl does")
    utils._set_mod("shift", False)
    check(back.cget("fg") == blue and ctl.play_btn.cget("fg") != amber, "Shift up, Ctrl still down")
    ctl.render_waveform()
    check(any("modhint" in (it.get("tags") or ()) for it in canvas.items), "the hint survives a redraw while held")
    utils._set_mod("control", False)
    check(back.cget("fg") == normal and not any("modhint" in (it.get("tags") or ()) for it in canvas.items),
          "all released: normal colors, no hint")


def test_round13(th, wt, media):
    print("\n-- round 13: log tail lines, no forced line metrics, damped card height, status time, debug tab last --")
    import logview_tab as lv
    import timing_panel as tp
    import tracked
    import utils
    # log viewer: a message arriving on its own starts its own line
    log = os.path.join(TMP, "tail.log")
    with open(log, "w") as f:
        f.write("[1] first @x/L01\n")
    text, tab = FakeText(), FakeTab()
    state = lv._LogViewState(tab, log)
    lv._full_reload(text, tab, state)
    with open(log, "a") as f:
        f.write("[2] Auto-saved song.mp3 @tracked:920/L02\n")
    lv._tail(text, tab, state, os.path.getsize(log))
    state.size = os.path.getsize(log)
    check(state.file_lines == ["[1] first @x/L01", "[2] Auto-saved song.mp3 @tracked:920/L02"],
          "the log viewer shows a newly written line on its own line (was glued to the one before)")
    with open(log, "a") as f:
        f.write("[3] half")
    lv._tail(text, tab, state, os.path.getsize(log)); state.size = os.path.getsize(log)
    with open(log, "a") as f:
        f.write(" line\n")
    lv._tail(text, tab, state, os.path.getsize(log))
    check(state.file_lines[-1] == "[3] half line", "...a line caught half-written is still joined up")

    # no forced "count -update" (the hang)
    src = open(tp.__file__).read()
    check('"update", "ypixels"' not in src, "the prewarm no longer forces Tk to measure every line at once")

    # damped WrapField height
    field = tp.WrapField(FakeWidget())
    heights = iter([3, 2, 3, 2, 3, 2])
    field.widget.count = lambda *a: (next(heights),)
    for _ in range(6):
        field.fit()
    check(field.widget.cget("height") == 3, "a card text field that would see-saw between heights settles on the taller")

    # status bar: date and time
    app = types.SimpleNamespace(status=FakeWidget())
    tracked.EditorApp.set_status(app, "Auto-saved x")
    shown = app.status.cget("text")
    check(re.match(r"^\d{4}-\d\d-\d\d \d\d:\d\d:\d\d  Auto-saved x$", shown) is not None,
          "status messages start with the date and time they appeared")
    app._update_title = lambda: None
    tracked.EditorApp._on_tab_modified(app, types.SimpleNamespace(dirty=True))
    check(app.status.cget("text") == "", "...and the Auto-saved one still clears on new changes")

    # debug tab stays last
    frames = ["a", "dbg", "b"]
    nb = types.SimpleNamespace(tabs=lambda: list(frames),
                               insert=lambda where, f: (frames.remove(f), frames.append(f)) if where == "end" else None)
    dbg = types.SimpleNamespace(frame="dbg")
    other = types.SimpleNamespace(frame="b")
    app2 = types.SimpleNamespace(_debug_tab=dbg, notebook=nb, tabs=[dbg, other])
    tracked.EditorApp._keep_debug_last(app2)
    check(frames[-1] == "dbg" and app2.tabs[-1] is dbg, "the debug log tab is moved back to the right end")

    # Play button, Transcribe tooltip, hint in the status row
    path = fresh_copy(media, "round13")
    ctl, canvas, text2, tab2 = bare_controller(wt, path)
    check(ctl.play_btn.cget("fg") == wt.TB_FG, "Play isn't colored unless Shift is held")
    ctl._play_state = "stopped"; ctl._update_play_controls()
    check(ctl.play_btn.cget("fg") == wt.TB_FG, "...also after play state updates")
    utils._set_mod("shift", True)
    lay = ctl._track_layout()
    hint = [it for it in canvas.items if "modhint" in (it.get("tags") or ()) and it["kind"] == "text"][0]
    check(lay["row_top"] <= hint["coords"][1] <= lay["track_top"], "the Shift/Ctrl hint is in the waveform's status row")
    utils._set_mod("shift", False)
    src_wt = open(wt.__file__).read()
    tip_src = src_wt[src_wt.index("_Tooltip(self.transcribe_btn"):][:500]
    check("Transcript" in tip_src and "timing track" in tip_src,
          "the Transcribe tooltip says the whole song goes into a new Transcript timing track")
    check(tp.REST_MODES == ("off", "group", "all") and tp.JOIN_MODES == ("off", "group", "all"),
          "Join> and <Join use the same mode names")


def test_diagnostics():
    print("\n-- diagnostics: breadcrumbs, stall report, feature switches --")
    import utils
    import tracked
    utils._crumbs.clear()
    for _ in range(3):
        utils.crumb("waveform render")
    utils.crumb("panel._build 70 cards")
    got = utils.recent_crumbs()
    check([(c[1], c[2]) for c in got] == [("waveform render", 3), ("panel._build 70 cards", 1)],
          "breadcrumbs: repeats are counted, not listed again")
    utils.DISABLED_FEATURES.add("prewarm")
    check(not utils.feature_on("prewarm") and utils.feature_on("fit"), "TRACKED_DISABLE switches a feature off")
    utils.DISABLED_FEATURES.discard("prewarm")
    out = io.StringIO()
    real_err, real_sleep = sys.stderr, time.sleep
    guard = tracked.InterruptGuard.__new__(tracked.InterruptGuard)
    guard._beat = time.monotonic() - 30
    guard._stalled_since = None
    calls = {"n": 0}

    def fake_sleep(sec):
        calls["n"] += 1
        if calls["n"] > 1:
            raise SystemExit
    try:
        sys.stderr, time.sleep = out, fake_sleep
        try:
            guard._stall_watch()
        except SystemExit:
            pass
    finally:
        sys.stderr, time.sleep = real_err, real_sleep
    text = out.getvalue()
    check("has not responded for" in text and "panel._build 70 cards" in text and "x3" in text,
          "a stall prints the last app steps (with repeat counts)")
    check(guard._stalled_since is not None, "...and while stuck a single Ctrl+C exits")


def test_stall_fixes(th, wt, media):
    print("\n-- the stall fixes: one-go clear, estimated card heights --")
    import timing_panel as tp
    path = fresh_copy(media, "stallfix")
    ctl, canvas, text, tab = bare_controller(wt, path)
    panel = ctl.panel
    big = ctl._new_track("Big")
    for i in range(50):
        ctl._add_mark("range", i * 1.0, i * 1.0 + 0.8, label=f"w{i}", track_id=big["id"])
    one = ctl._new_track("One")
    ctl._add_mark("range", 60.0, 80.0, label="a long label " * 20, track_id=one["id"])
    ctl.selected = ("track", big["id"]); ctl.render_waveform(); run_afters()
    frames = [c["frame"] for c in panel.cards.values()]
    destroyed = []
    for fr in frames:
        fr.destroy = (lambda f_: (lambda: destroyed.append(f_)))(fr)
    deletes = []
    real_delete = panel.canvas.delete
    panel.canvas.delete = lambda *a: deletes.append(a) or real_delete(*a)
    AFTERS.clear()
    ctl.selected = ("track", one["id"]); ctl.render_waveform()
    panel.canvas.delete = real_delete
    check(deletes and deletes[0] == ("all",) and not destroyed,
          "switching tracks: the old cards leave the list in one go, nothing destroyed card by card first")
    check(len(panel.cards) == 1, "...and the new track is shown right away")
    run_afters()
    check(len(destroyed) == len(frames), "...the old cards' Python side is tidied up afterwards, a few at a time")
    field = tp.WrapField(FakeWidget())
    field.widget.winfo_width = lambda: 1                  # not laid out yet
    field.widget.count = lambda *a: (8,)                  # what Tk would say at 1 pixel wide
    field.estimate_px = 800
    field.estimate_lines = lambda w: 2
    field.fit()
    check(field.widget.cget("height") == 2,
          "a card text field not laid out yet takes its estimated height (not 8 lines from a 1-pixel width)")
    field.widget.winfo_width = lambda: 700
    field.widget.count = lambda *a: (3,)
    field.fit()
    check(field.widget.cget("height") == 3, "...and the real one once Tk has laid it out")


def test_card_fits_panel(th, wt, media):
    print("\n-- a card is never taller than the panel --")
    import timing_panel as tp
    path = fresh_copy(media, "cardfit")
    ctl, canvas, text, tab = bare_controller(wt, path)
    panel = ctl.panel
    one = ctl._new_track("One")
    m = ctl._add_mark("range", 60.0, 80.0, label="a long label " * 40, track_id=one["id"])
    ctl.selected = ("track", one["id"]); ctl.render_waveform(); run_afters()
    panel.canvas.winfo_height = lambda: 200
    panel.canvas.winfo_width = lambda: 900
    panel._on_list_configure()
    field = panel.cards[m["id"]]["text"]
    cap = panel.max_field_lines()
    check(cap < tp.WrapField.MAX_LINES and field.max_lines == cap,
          f"in a 200-px panel a card's text may grow to {cap} lines (the card stays shorter than the panel)")
    field.widget.winfo_width = lambda: 700
    field.widget.count = lambda *a: (12,)
    field.fit()
    check(field.widget.cget("height") == cap, "...a long label stops there (the field scrolls inside)")
    panel.canvas.winfo_height = lambda: 140
    panel._on_list_configure()
    check(field.max_lines == panel.max_field_lines() < cap and field.widget.cget("height") == field.max_lines,
          "making the panel smaller shrinks the cap and the tall fields with it")
    panel.canvas.winfo_height = lambda: 600
    panel._on_list_configure()
    check(field.max_lines == panel.max_field_lines() > cap and field.widget.cget("height") == min(12, field.max_lines),
          "...and a taller panel lets a track's only card grow again")
    two = ctl._add_mark("range", 82.0, 84.0, label="short", track_id=one["id"])
    ctl.render_waveform(); run_afters()
    check(panel.max_field_lines() == tp.MULTI_CARD_LINES and field.max_lines == tp.MULTI_CARD_LINES
          and field.widget.cget("height") <= tp.MULTI_CARD_LINES,
          "with several cards in the track, card text fields are 1-3 lines (they scroll inside)")
    f2 = tp.WrapField(FakeWidget())
    f2.widget.winfo_width = lambda: 1
    inserted = []
    f2.widget.insert = lambda *a: inserted.append(a)
    f2.insert(0, "a long label " * 50)
    check(not inserted and f2.get().startswith("a long label"),
          "a card's text waits outside the Tk field until the field has a real width")
    f2.widget.winfo_width = lambda: 600
    f2._on_configure()
    check(inserted and inserted[0][1].startswith("a long label"), "...and goes in once it has one")


def test_card_list(th, wt, media):
    print("\n-- the card list: its own canvas over the text panel --")
    path = fresh_copy(media, "cardlist")
    ctl, canvas, text, tab = bare_controller(wt, path)
    panel = ctl.panel
    tr = ctl._new_track("Words")
    ids = [ctl._add_mark("range", i * 2.0, i * 2.0 + 1.0, label=f"w{i}", track_id=tr["id"])["id"] for i in range(6)]
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    check(panel.list is not None and panel.list._cfg.get("_placed", True) and len(panel.canvas.windows) == 6,
          "a track's cards are window items in the card list's own canvas")
    check(not any(c["frame"] in text.windows for c in panel.cards.values()), "...not embedded in the text panel")
    heights = {ids[0]: 40, ids[1]: 100, ids[2]: 40, ids[3]: 40, ids[4]: 40, ids[5]: 40}
    for mid, h in heights.items():
        panel.cards[mid]["frame"].winfo_reqheight = (lambda h_: (lambda: h_))(h)
    panel._relayout()
    ys = [panel.canvas.windows[panel.cards[mid]["item"]]["coords"][1] for mid in ids]
    check(ys[1] - ys[0] == 40 + 3 and ys[2] - ys[1] == 100 + 3, "cards are stacked one below the other by their heights")
    panel.canvas.winfo_width = lambda: 777
    panel.canvas.winfo_height = lambda: 120
    panel._on_list_configure()
    check(all(panel.canvas.windows[c["item"]].get("width") == 777 for c in panel.cards.values()),
          "cards take the list's width")
    panel._relayout()
    panel._see(ids[5])
    check(panel.canvas.moved_to is not None and panel.canvas.moved_to > 0.3, "seeing a card scrolls the list to it")
    extra = ctl._add_mark("range", 30.0, 31.0, label="new", track_id=tr["id"])
    ctl.render_waveform()
    card = panel.cards[extra["id"]]
    card["frame"].winfo_reqheight = lambda: 1           # a fresh card: Tk hasn't sized it yet
    card["shown"] = False
    panel.canvas.itemconfigure(card["item"], state="hidden")
    panel._relayout()
    check(panel.canvas.windows[card["item"]].get("state") == "hidden" and extra["id"] not in panel._positions,
          "a card is kept hidden until Tk has worked out its size (no stack of thin lines)")
    card["frame"].winfo_reqheight = lambda: 50
    run_afters()
    check(panel.canvas.windows[card["item"]].get("state") == "normal" and extra["id"] in panel._positions,
          "...then shown in its place")
    ctl.delete_mark_by_id(extra["id"]); ctl.render_waveform(); run_afters()
    ctl.selected = None; ctl.render_waveform(); run_afters()
    check(panel.mode == "info", "no track selected: the info text again (the list is hidden)")
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    check(len(panel.canvas.windows) == 6 and card_order(panel) == ids, "...and back")


def test_busy_report():
    print("\n-- busy report: CPU by thread and the app steps behind it --")
    import utils
    import tracked
    threads = tracked.InterruptGuard._thread_cpu()
    check(isinstance(threads, dict) and (not threads or "MainThread" in threads),
          "per-thread CPU time is read from /proc (by thread name)")
    guard = tracked.InterruptGuard.__new__(tracked.InterruptGuard)
    guard._busy = 0.0
    t0 = time.monotonic()
    guard._busy_watch(t0)                          # starts a window
    utils._crumbs.clear()
    for i in range(30):
        utils.crumb(f"panel._relayout {i} shown, 0 waiting, 3 ms")
    guard._busy = 4.0                              # 4 s of the 5 the main loop was late
    out = io.StringIO()
    real = sys.stderr
    try:
        sys.stderr = out
        guard._busy_watch(t0 + 5.1)
    finally:
        sys.stderr = real
    text = out.getvalue()
    check("busy -- main loop" in text and "panel._relayout # shown, # waiting, # ms" in text and "30" in text,
          "a busy stretch prints which steps ran how often (numbers folded together)")
    out = io.StringIO()
    try:
        sys.stderr = out
        guard._busy_watch(t0 + 10.2)               # an idle window: nothing printed
    finally:
        sys.stderr = real
    check(out.getvalue() == "", "...and nothing when it's idle")


def test_dialog_colors():
    print("\n-- Tk's built-in dialogs get readable colors --")
    import tracked

    class Root:
        def __init__(self):
            self.options = []

        def option_add(self, pattern, value, priority=None):
            self.options.append((pattern, value, priority))

    root = Root()
    tracked.apply_dialog_colors(root)
    opts = {p: (v, pr) for p, v, pr in root.options}
    check(opts.get("*TkFDialog*foreground", (None,))[0] == tracked.DIALOG_FG
          and opts.get("*TkFDialog*Canvas.background", (None,))[0] == tracked.DIALOG_FIELD_BG,
          "the file Open/Save dialog: dark text on a light file list")
    check(all(f"*{cls}*foreground" in opts and f"*{cls}*background" in opts and f"*{cls}*Entry.background" in opts
              for cls in ("TkFDialog", "TkChooseDir", "TkColorDialog", "Dialog", "Toplevel")),
          "...and the same for the directory, color, message-box and simpledialog windows")
    check(all(pr == "interactive" for _p, _v, pr in root.options),
          "added above the desktop's X-resource colors (userDefault priority)")
    check(not any(p in ("*foreground", "*background", "*Foreground", "*Background") for p in opts),
          "scoped to dialog windows: the main window's look is unchanged")
    names = [p for p, _v, _pr in root.options if p.startswith("*TkFDialog*")]
    check(names.index("*TkFDialog*Canvas.background") > names.index("*TkFDialog*background"),
          "the specific field backgrounds come after the generic background")
    src = open(os.path.join(os.path.dirname(os.path.abspath(tracked.__file__)), "tracked.py")).read()
    init = src[src.index("class EditorApp"):]
    check("apply_dialog_colors(self)" in init
          and init.index("apply_dialog_colors(self)") < init.index("self._build_ui()"),
          "the app installs them right after creating the root window")


# ---------------------------------------------------------------------------

def main():
    th, aa, wt, used_fake_sf = load_modules()
    print(f"Testing trackED waveform_tab v{wt.VERSION}  (temp dir {TMP})")
    if used_fake_sf:
        print("  note: soundfile not installed -- using a WAV-only stand-in for the stem tests")

    test_time_formatting(th)
    test_rebucket_peaks(th)
    test_overlap_lanes(th)
    test_exports(th)
    test_split_merge_planning(th)
    test_model_choice_and_regions(aa)
    test_debug_level_cli()
    test_image_viewer()
    test_tab_dirty_marker()
    test_dial_geometry_sash()
    test_dialog_colors()
    test_word_adjustments(th)
    layout_path = test_xlayout_logic()
    test_xlayout_view(layout_path)
    test_xlayout_round3(layout_path)
    test_logview_wrap()

    if not HAVE_FFMPEG:
        print("\n-- media tests --\n  SKIP: ffmpeg/ffprobe not found on PATH")
    else:
        media = make_media("tone", 10.0)
        test_combined_cache(th, media)
        test_metadata(th, TMP)
        test_load_and_deep_zoom(th, wt, media)
        test_mark_interactions(th, wt, media)
        test_timing_tracks(th, wt, media)
        test_split_merge_controller(th, wt, media)
        test_timing_panel(th, wt, media)
        test_voices(th, wt, media)
        test_word_panel(th, wt, media)
        test_round4(th, wt, media, os.path.join(TMP, "xlights_rgbeffects.xml"))
        test_audio_edges(th, wt)
        test_round6(th, wt, media)
        test_view_and_slices(th, wt, media)
        test_card_speed(th, wt, media)
        test_round10(th, wt, media)
        test_round11(th, wt, media)
        test_waveform_mod_hints(th, wt, media)
        test_round13(th, wt, media)
        test_diagnostics()
        test_stall_fixes(th, wt, media)
        test_card_fits_panel(th, wt, media)
        test_card_list(th, wt, media)
        test_busy_report()
        test_playback_loop_and_cursor(th, wt, media)
        test_cursor_playhead_model(th, wt, media)
        test_shift_click_anchor(th, wt, media)
        test_stem_tracks(th, wt, media)
        test_sash_hints_and_save_protection(media)
        test_undo_routing_and_card_style(th, wt, media)
        test_toolbar_layout(th, wt, media)
        test_cards_delete_repeat_colors(th, wt, media)
        test_title_dirty_autosave(th, wt, media)
        test_card_editor_extras(th, wt, media)
        test_round5(th, wt, media)
        test_round7(th, aa, wt, media)
        test_round8(th, aa, wt, media)
        test_round9(th, aa, wt, media)
        test_stems_and_transcription(th, aa, wt, media)

    shutil.rmtree(TMP, ignore_errors=True)
    print(f"\n{'=' * 50}")
    print(f"{PASS_COUNT} passed, {len(FAILURES)} failed")
    if FAILURES:
        print("\nFailures:")
        for f in FAILURES:
            print(f"  - {f}")
        sys.exit(1)
    print("All tests passed.")


if __name__ == "__main__":
    main()
