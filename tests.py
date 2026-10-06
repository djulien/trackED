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

    def after_idle(self, fn, *args):
        """Like Tk: runs later (run_afters), not never."""
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

    def add_separator(self):
        self.entries.append({"kind": "separator", "label": ""})
    def tk_popup(self, *a): pass

    def labels(self):
        return [e["label"] for e in self.entries if e.get("kind") != "separator"]

    def entry(self, label):
        return next(e for e in self.entries if e.get("label") == label)


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
    simpledialog.askinteger = lambda *a, **k: None
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
    torch.from_numpy = torch.wrap
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
    panel._split(m1["id"], how="text")
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
    start2 = round(paused_at + 5.0, 3)
    time.sleep(0.05)
    ctl.toggle_play()                                  # pause again
    paused2 = ctl.cursor_time
    ctl._ctrl_on_play = True
    ctl.toggle_play()
    check(ctl.engine.calls[-1][0] == round(paused2, 3), "while paused, Ctrl+Play resumes from the paused spot")
    time.sleep(0.05)
    ctl.toggle_play()                                  # pause
    ctl.toggle_play()                                  # bare Play
    check(ctl._play_state == "playing" and ctl.engine.calls[-1][0] == start2,
          "while paused, bare Play starts again from where Play started")
    ctl.toggle_play(); ctl.stop_play()
    check(not hasattr(ctl, "play_stop_btn"), "there is no Reset button any more")

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
    real_missing = wt.deps.missing
    wt.deps.missing = lambda include_broken=False: [wt.deps.BY_KEY["demucs"], wt.deps.BY_KEY["librosa"]]
    ctl._refresh_playback_availability()
    shown = (ctl.install_btn.packed and "demucs" in ctl._install_tip.text and "librosa" in ctl._install_tip.text
             and "Install" in ctl.install_btn.cget("text"))
    wt.deps.missing = lambda include_broken=False: []
    saved_pm = dict(th.PLAYBACK_MISSING); th.PLAYBACK_MISSING.clear()
    ctl._refresh_playback_availability()
    hidden = not ctl.install_btn.packed
    th.PLAYBACK_MISSING.update(saved_pm)
    wt.deps.missing = real_missing
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
    check(kids.index(card["play"]) < kids.index(card["start"]) and "stop" not in card,
          "a card's Play sits left of the Start/End times (no Stop button)")
    right = [kids.index(card["split"]), kids.index(card["merge"]), kids.index(card["delete"])]
    check(min(right) > kids.index(card["end_rsnap"]), "Split / Merge / Delete stay on the right")
    check(getattr(card["play"], "_loop_hover", False), "card Play buttons are marked for the Shift-key loop cursor")

    # card Play: pause, then bare Play restarts the card, Ctrl+Play resumes
    card["play"]._cfg["command"]()
    check(ctl._play_state == "playing" and ctl._play_mark_id == a["id"], "a card's Play plays its mark")
    card["play"]._cfg["command"]()      # pause
    check(ctl._play_state == "paused", "...and pauses it")
    at = [it for it in canvas.items if it["kind"] == "text" and "cursor_at" in (it.get("tags") or ())]
    check(at and abs(at[0]["coords"][0] - ctl._play_position / 100 * 800) < 1.0,
          "while paused, the '@' tag sits at the playhead")
    panel._ctrl_on_play = True
    card["play"]._cfg["command"]()
    check(ctl._play_state == "playing" and ctl.engine.calls[-1][0] == round(ctl._paused_at, 3),
          "Ctrl+Play on the paused card resumes it")
    card["play"]._cfg["command"]()      # pause
    card["play"]._cfg["command"]()      # bare Play
    check(ctl._play_state == "playing" and ctl.engine.calls[-1][0] == round(a["start"], 3),
          "bare Play on the paused card starts it again from its start")
    ctl.stop_play()

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
    entry = next(e for e in ctl.stems_menu.entries if e["label"] == "New range from @cursor")
    check(entry["label"] == "New range from @cursor", "the Stems menu offers \"New range from @cursor\"")
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
    labels = [e["label"] for e in menu.entries]
    check(labels[0].startswith("Split at @cursor") and labels[1].startswith("Split at text cursor")
          and labels[2:] == ["Split in half", "Split selected phrase", "Split into words (5)"]
          and menu.entry("Split selected phrase").get("state") == "normal",
          "Split \u25be offers @cursor / text cursor / half / selected phrase / words")
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
    check([e["label"] for e in checks] == ["All voices"] + ctl.voices and checks[0]["variable"].get() is False
          and checks[1]["variable"].get() is True,
          "...with \"All voices\" and a check item per voice (checked when assigned)")
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
    check(panel.cards[b["id"]]["voice"].cget("text") == "All voices \u25be", "...and follows changes (none set: All voices)")
    ctl.set_mark_voices(b["id"], ["Lead"])
    panel._fill_voice_menu(b["id"], card["voice_menu"])
    check([e["label"] for e in card["voice_menu"].entries if e.get("kind") == "check"] == ["All voices"] + ctl.voices,
          "the Voice \u25be menu lists All voices and the voices")
    ctl.set_mark_voices(ctl.track_marks(tr["id"])[0]["id"], [])     # one card without a voice
    shown_all = list(panel.cards)
    panel.voice_filter_var.set("Lead"); panel._on_voice_filter()
    check(list(panel.cards) == [m["id"] for m in ctl.track_marks(tr["id"]) if "Lead" in (m.get("voices") or [])]
          and len(panel.cards) < len(shown_all), "Show: <voice> limits the cards to that voice")
    check("of" in panel._header_label.cget("text"), "...and the header says how many are shown")
    panel.voice_filter_var.set("All voices")
    panel._on_voice_filter()
    check(len(panel.cards) == 1 and all(not ctl.mark_by_id(mid).get("voices") for mid in panel.cards),
          "Show: All voices shows the cards with no voice set (they're for all voices)")
    panel.voice_filter_var.set("All cards"); panel._on_voice_filter()
    check(list(panel.cards) == shown_all, "Show: All cards shows every card again")


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
    check(order[:-1] == ["\u2196", "[", "\u21e4", "\u2212", "+", "\u2197", "@", "\u2199", "\u2212", "+", "\u21e5", "]", "\u2198", "@"]
          and card["tbtns"][-1] is card["lock"],
          "Start/End buttons: the earlier ones left of the box, the later ones and @ right of it (then the lock)")
    check(card["join"].cget("text") == "<Join none" and card["rest"].cget("text") == "Join> none",
          "the buttons are named <Join (Start side) and Join> (End side)")
    check(card["frame"].cget("bg") != "#f4f4f4" and tp.contrast_fg(card["frame"].cget("bg")) == tp.LIGHT_TEXT
          and card["start"].cget("bg") == tp.ENTRY_BG, "cards are dark (light text), like the panel around them")

    # #5 voice button
    check(tp.voice_button_text([], "hello") == "All voices \u25be", "no voice set: the card is for All voices")
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
                                destroy=lambda: calls.append("slow destroy"), _w=".", children={},
                                tk=types.SimpleNamespace(call=lambda *a: calls.append(a), deletecommand=lambda n: None))
    tracked.EditorApp._teardown_and_destroy(app)
    check(calls == ["withdraw", "tab", ("destroy", ".")],
          "quitting: hide the window, let plugins drop their widgets, then destroy everything in one Tk call")


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
    check(re.match(r"^Auto-saved x   \(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d\)$", shown) is not None,
          "status messages end with the date and time they appeared")
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
    real_fast = tp.fast_destroy
    tp.fast_destroy = lambda w: destroyed.append(w)
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
    tp.fast_destroy = real_fast
    check(all(f in destroyed for f in frames), "...the old cards are destroyed afterwards, a batch at a time")
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
    guard._busy_watch(t0)                          # off by default: does nothing
    check(getattr(guard, "_busy_window_start", None) is None, "busy reports are off by default")
    tracked.BUSY_REPORTS_CLI["on"] = True          # as with -busy
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
    tracked.BUSY_REPORTS_CLI["on"] = None


def test_fast_destroy():
    print("\n-- fast_destroy: one Tk call for a whole widget tree --")
    import utils
    calls, deleted = [], []
    fake_tk = types.SimpleNamespace(call=lambda *a: calls.append(a), deletecommand=lambda n: deleted.append(n))
    root = types.SimpleNamespace(_w=".list", _name="list", tk=fake_tk, _tclCommands=["cb1"], children={})
    kids = [types.SimpleNamespace(_w=f".list.k{i}", _name=f"k{i}", tk=fake_tk, _tclCommands=[f"k{i}cb"],
                                  children={}) for i in range(3)]
    root.children = {k._name: k for k in kids}
    master = types.SimpleNamespace(children={"list": root})
    root.master = master
    utils.fast_destroy(root)
    check(calls == [("destroy", ".list")], "a widget tree is destroyed with a single Tk call")
    check(sorted(deleted) == ["cb1", "k0cb", "k1cb", "k2cb"] and "list" not in master.children,
          "...its callbacks are released and it's detached from its parent")


def test_input_methods():
    print("\n-- the desktop input method (ibus/XIM) is off unless chosen --")
    import utils
    import tracked
    calls = []
    root = types.SimpleNamespace(tk=types.SimpleNamespace(call=lambda *a: calls.append(a)))
    utils.set_preference(tracked.PREF_INPUT_METHODS, False)
    check(tracked.apply_input_methods(root) is False and calls[-1] == ("tk", "useinputmethods", "-displayof", root, 0),
          "by default Tk doesn't use the X input method (ibus kept the app waiting with many cards)")
    utils.set_preference(tracked.PREF_INPUT_METHODS, True)
    check(tracked.apply_input_methods(root) is True and calls[-1][-1] == 1, "...a preference turns it on")
    utils.set_preference(tracked.PREF_INPUT_METHODS, False)


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


def test_round14(th, aa, wt, media):
    print("\n-- round 14: deps/Install, restart, drops, stems decode, play, split, multi-select, voices --")
    import deps
    import tracked
    import timing_panel as tp

    # deps registry (#4/#7/#8/#11)
    keys = [d["key"] for d in deps.DEPENDENCIES]
    check(all(k in keys for k in ("demucs", "librosa", "faster-whisper", "tkinterdnd2", "psutil", "ffmpeg")),
          "the Install list includes demucs, librosa, faster-whisper, tkinterdnd2, psutil and ffmpeg")
    check(all(d.get("purpose") and d.get("size") for d in deps.DEPENDENCIES), "each entry says what it's for and its size")
    real_spec = deps._importable
    deps._importable = lambda name: name not in ("librosa", "demucs")
    names = [d["key"] for d in deps.missing()]
    deps._importable = real_spec
    check("librosa" in names and "demucs" in names and "numpy" not in names, "missing() reports what isn't importable")
    check("--no-warn-script-location" in deps.pip_args(["x"]) and deps.pip_args(["x"])[0] == sys.executable,
          "pip runs with this Python and without the not-on-PATH warning (PATH is left alone)")
    check("trackED.sh" in deps.explain_pip_failure("error: externally-managed-environment"),
          "a system-managed Python gets a plain explanation")
    cmd, manual = deps.program_install_command(deps.BY_KEY["ffmpeg"])
    check(bool(manual), "ffmpeg has an install command or instructions on this system")
    ok, failed = deps.install(["nonexistent-key"])
    check(ok == [] and failed == [], "unknown keys are ignored")

    # Install dialog + restart offer (#6, #8)
    p = fresh_copy(media, "r14_install")
    ctl, canvas, text, tab = open_controller(wt, p)
    real_missing = deps.missing
    deps.missing = lambda include_broken=False: [deps.BY_KEY["librosa"], deps.BY_KEY["ffmpeg"]]
    try:
        dlg = wt.InstallDialog(canvas)
        check(dlg.selected() == ["librosa", "ffmpeg"], "the dialog lists each missing package, all checked")
        dlg.vars["ffmpeg"].set(False); dlg._sync_all()
        check(dlg.selected() == ["librosa"] and dlg.all_var.get() is False, "...each can be unchecked (multi-select)")
        dlg.all_var.set(True); dlg._toggle_all()
        check(dlg.selected() == ["librosa", "ffmpeg"], "...and \"All missing\" checks them all again")
        ctl._refresh_playback_availability()
        check(ctl.install_btn.packed and ctl.install_btn.cget("text") == "\u26a0 Install",
              "the toolbar button reads \u26a0 Install")
        restarts = []
        canvas.restart = lambda: restarts.append(1)
        ctl._install_finished(["librosa"], [])
        check(restarts == [] and ctl.install_btn.cget("text") == "\u27f3 Restart",
              "after an install the toolbar button becomes Restart (no message box that could hide)")
        ctl._on_install_clicked()
        check(restarts == [1], "clicking Restart restarts")
    finally:
        deps.missing = real_missing
    deps.missing = lambda include_broken=False: [deps.BY_KEY["librosa"]]
    try:
        ctl_i, _ci, text_i, _ti = open_controller(wt, fresh_copy(media, "r14_info"))
        info = text_i.get("1.0", "end")
    finally:
        deps.missing = real_missing
    check("Missing dependencies: librosa." in info and "Install button in the upper right corner" in info,
          "the text panel says briefly what's missing and where the Install button is")
    from pathlib import Path
    check(tracked.restart_command(["tracked.py", "-debug", "3", "song.mp3", "-fresh"])[1:]
          == [str(Path(tracked.__file__).resolve()), "-debug", "3"],
          "restart keeps the options but not file names or -fresh (the session reopens files)")

    # drops (#2)
    opened = []
    app = types.SimpleNamespace(tk=types.SimpleNamespace(splitlist=lambda d: d.split("|")),
                                open_file=lambda p_: opened.append(p_))
    ev = types.SimpleNamespace(data=p + "|/no/such/file", action="copy")
    check(tracked.EditorApp._on_drop(app, ev) == "copy" and opened == [p],
          "a drop opens the file and returns the copy action (Windows needs one)")
    reg = []
    w1 = types.SimpleNamespace(_own_drop=True, drop_target_register=lambda *a: reg.append("own"))
    w2 = types.SimpleNamespace(drop_target_register=lambda *a: reg.append("w2"), dnd_bind=lambda *a: None)
    app2 = types.SimpleNamespace(_on_drop=None)
    old_has = tracked.HAS_DND
    tracked.HAS_DND = True
    tracked.DND_FILES = "DND_Files"
    tracked.EditorApp._register_drops(app2, w1)
    tracked.EditorApp._register_drops(app2, w2)
    tracked.EditorApp._register_drops(app2, w2)
    tracked.HAS_DND = old_has
    check(reg == ["w2"], "each tab widget is registered once; the waveform canvas keeps its own drop handling")

    # stems without ffprobe (#12)
    err = FileNotFoundError(2, "The system cannot find the file specified")
    text_ = aa.explain_error(err, "Stem separation")
    check("ffmpeg" in text_ and "Install" in text_, "WinError 2 is explained: ffmpeg missing, use Install")
    check("can't be found" in aa.explain_error(FileNotFoundError(2, "x", "/a/song.mp3")),
          "...a missing audio file is named as such")
    data = aa.decode_for_demucs(media, 8000, 2)
    check(data.shape[0] == 2 and abs(data.shape[1] / 8000 - 10.0) < 0.1, "stems decode the audio themselves")
    import shutil as _sh
    real_which = aa.shutil.which
    aa.shutil.which = lambda name: None
    try:
        wav = make_media("r14_wav", 2.0)
        data2 = aa.decode_for_demucs(wav, 8000, 2)
        check(data2.shape[0] == 2 and abs(data2.shape[1] / 8000 - 2.0) < 0.05,
              "...and without ffmpeg/ffprobe on PATH they fall back to soundfile (+ resample)")
    finally:
        aa.shutil.which = real_which
    src = open(os.path.join(HERE, "audio_analysis.py")).read()
    check("AudioFile(" not in src, "demucs' ffprobe-based AudioFile reader is no longer used")

    # dirty first (#1, defensive)
    ctl2, _c2, _t2, tab2 = bare_controller(wt, fresh_copy(media, "r14_dirty"), 20.0)
    tab2.dirty = False
    real_push = ctl2._push_mark_history
    ctl2._push_mark_history = lambda: (_ for _ in ()).throw(RuntimeError("boom"))
    ctl2._add_mark("point", 1.0, None)
    ctl2._push_mark_history = real_push
    check(tab2.dirty, "a change marks the tab unsaved even if undo bookkeeping fails")

    # play (#14)
    ctl3, c3, _t3, _tab3 = bare_controller(wt, fresh_copy(media, "r14_play"), 100.0)
    ctl3.cursor_time = 10.0
    ctl3.toggle_play(); time.sleep(0.05); ctl3.toggle_play()
    paused = ctl3.cursor_time
    ctl3.cursor_time = 40.0                                    # moved while paused
    ctl3.toggle_play()
    check(ctl3.engine.calls[-1][0] == 40.0, "paused + Play after moving the @cursor plays from the @cursor")
    ctl3.stop_play()

    # Split menu (#10)
    tr = ctl3._new_track("Lyrics")
    mk = ctl3._add_mark("range", 10.0, 20.0, label="one two three four", track_id=tr["id"])
    ctl3.selected = ("track", tr["id"]); ctl3.render_waveform(); run_afters()
    ctl3.cursor_time = 12.5
    ctl3.panel._split(mk["id"], how="time")
    first = ctl3.mark_by_id(mk["id"])
    check(abs(first["end"] - 12.5) < 1e-9, "Split at @cursor splits at the @cursor, whatever the text cursor")
    ctl3.panel._split(mk["id"], how="half")
    check(abs(ctl3.mark_by_id(mk["id"])["end"] - 11.25) < 0.5, "Split in half splits in the middle")
    panel_src = open(os.path.join(HERE, "timing_panel.py")).read()
    check("Nudge size:" in panel_src and "Step (s):" not in panel_src, "the header says Nudge size:")
    check("Ctrl+click the waveform to place @cursor and Split" not in panel_src, "the misleading hint is gone")

    # merge with the next visible card (A1)
    ctl4, _c4, _t4, _tab4 = bare_controller(wt, fresh_copy(media, "r14_merge"), 100.0)
    tr4 = ctl4._new_track("V")
    a = ctl4._add_mark("range", 1.0, 2.0, label="a", track_id=tr4["id"])
    b = ctl4._add_mark("range", 2.0, 3.0, label="b", track_id=tr4["id"])
    c = ctl4._add_mark("range", 3.0, 4.0, label="c", track_id=tr4["id"])
    ctl4.set_mark_voices(a["id"], ["Lead"]); ctl4.set_mark_voices(c["id"], ["Lead"])
    ctl4.selected = ("track", tr4["id"]); ctl4.render_waveform(); run_afters()
    ctl4.panel.voice_filter_var.set("Lead"); ctl4.panel._on_voice_filter()
    ctl4.panel._merge_next(a["id"])
    check(ctl4.mark_by_id(c["id"]) is None and ctl4.mark_by_id(b["id"]) is not None
          and ctl4.mark_by_id(a["id"])["label"] == "a c", "Merge \u2193 merges with the next visible card")

    # multi-select, copy/cut/paste/move (#15)
    ctl5, c5, _t5, tab5 = bare_controller(wt, fresh_copy(media, "r14_multi"), 100.0)
    src_t = ctl5._new_track("Lead")
    dst_t = ctl5._new_track("Backup")
    ms = [ctl5._add_mark("range", float(i), i + 0.8, label=f"w{i}", track_id=src_t["id"]) for i in range(1, 6)]
    ctl5.selected = ("mark", ms[1]["id"])
    ctl5.extend_selection(ms[3], toggle=False)
    check(ctl5.selected_mark_ids() == [m["id"] for m in ms[1:4]], "Shift+click selects a run of marks in the track")
    ctl5.extend_selection(ms[2], toggle=True)
    check(ms[2]["id"] not in ctl5.selected_mark_ids() and len(ctl5.selected_mark_ids()) == 2,
          "Ctrl+click toggles one mark")
    check(ctl5._is_highlighted("mark", ms[1]["id"]) and ctl5._is_highlighted("mark", ms[3]["id"]),
          "every selected mark is highlighted")
    n = ctl5.copy_selection()
    ctl5.selected = ("track", dst_t["id"])
    pasted = ctl5.paste_marks()
    check(n == 2 and [(m["start"], m["label"], m["track_id"]) for m in pasted]
          == [(2.0, "w2", dst_t["id"]), (4.0, "w4", dst_t["id"])] and len({m["id"] for m in pasted} & {m["id"] for m in ms}) == 0,
          "Ctrl+C / Ctrl+V copies marks into the selected track at the same times (new ids)")
    ctl5.cursor_time = 50.0
    at = ctl5.paste_marks(dst_t["id"], at_cursor=True)
    check(at[0]["start"] == 50.0 and at[1]["start"] == 52.0, "Paste at @cursor shifts them to start there")
    hist = ctl5._mark_history_index
    ctl5.selected = ("mark", ms[0]["id"]); ctl5._multi = [ms[0]["id"], ms[4]["id"]]
    moved = ctl5.move_selection_to_track(dst_t["id"])
    check(all(m["track_id"] == dst_t["id"] for m in moved) and ctl5._mark_history_index == hist + 1,
          "Move to Track moves the selected marks (one undo step)")
    ctl5.undo_marks()
    check(ctl5.mark_by_id(ms[0]["id"])["track_id"] == src_t["id"], "...and undo moves them back")
    ctl5.selected = ("mark", ms[0]["id"]); ctl5._multi = [ms[0]["id"], ms[1]["id"]]
    copies = ctl5.move_selection_to_track(dst_t["id"], keep=True)
    check(len(copies) == 2 and ctl5.mark_by_id(ms[0]["id"])["track_id"] == src_t["id"],
          "Copy to Track leaves the originals")
    ctl5.selected = ("mark", ms[0]["id"]); ctl5._multi = [ms[0]["id"], ms[1]["id"]]
    tab5.dirty = False
    ctl5.cut_selection()
    check(ctl5.mark_by_id(ms[0]["id"]) is None and len(wt._MARK_CLIPBOARD["marks"]) == 2 and tab5.dirty,
          "Cut removes the marks and keeps them for pasting")
    ctl5.selected = ("mark", ms[2]["id"]); ctl5._multi = [ms[2]["id"], ms[3]["id"]]
    ctl5._on_key_delete(Event())
    check(ctl5.mark_by_id(ms[2]["id"]) is None and ctl5.mark_by_id(ms[3]["id"]) is None, "Delete removes the whole selection")
    layout = ctl5._track_layout()
    lead_y = None
    for zone_y in range(0, 400):
        z, t_ = ctl5._track_zone_at_y(zone_y)
        if z == "track" and t_ == src_t["id"]:
            lead_y = zone_y + 2
            break
    ctl5.selected = ("mark", ms[4]["id"]); ctl5._multi = []
    before = ctl5.cursor_time
    ctl5._on_ctrl_press(Event(x=int(ms[4]["start"] / 100 * 800) + 3, y=lead_y))
    check(ctl5.cursor_time == before, "Ctrl+click on a mark in a track selects instead of moving the @cursor")
    ctl5._on_ctrl_press(Event(x=int(80 / 100 * 800), y=lead_y))
    check(abs(ctl5.cursor_time - 80.0) < 0.5, "Ctrl+click on an empty part still moves the @cursor")

    # per-voice export (A2)
    marks = [
        {"id": "1", "type": "range", "start": 0.0, "end": 1.0, "label": "all sing"},
        {"id": "2", "type": "range", "start": 1.0, "end": 2.0, "label": "lead line", "voices": ["Lead"]},
        {"id": "3", "type": "range", "start": 2.0, "end": 3.0, "label": "(ooh)"},
        {"id": "4", "type": "range", "start": 3.0, "end": 4.0, "label": "both", "voices": ["Lead", "voice 2"]},
    ]
    check(th.effective_voices(marks[0]) == [] and th.effective_voices(marks[2]) == ["voice 2"],
          "no voice set = all voices; all-parentheses text implies voice 2")
    out = th.voice_export_tracks("Lyrics", marks, ["Lead", "voice 2", th.ALL_VOICES_NAME, th.ANY_VOICE])
    got = {name: [m["id"] for m in ms_] for name, ms_ in out}
    check(got == {"Lyrics - Lead": ["1", "2", "4"], "Lyrics - voice 2": ["1", "3", "4"],
                  "Lyrics - All voices": ["1"], "Lyrics": ["1", "2", "3", "4"]},
          "per-voice tracks: a voice's cards plus the All-voices cards; All voices only; every card")
    out2 = th.voice_export_tracks("Lyrics", marks, ["Lead"], all_voices_in_each=False)
    check([m["id"] for m in out2[0][1]] == ["2", "4"], "...or a voice's own cards only")
    check(th.overlap_count([marks[0], dict(marks[1], start=0.5)]) == 1 and th.overlap_count(marks) == 0,
          "overlapping cards in an exported track are counted (xLights warning)")
    ctl6, c6, _t6, _tab6 = bare_controller(wt, fresh_copy(media, "r14_voices"), 10.0)
    tr6 = ctl6._new_track("Lyrics")
    for m in marks:
        ctl6._add_mark("range", m["start"], m["end"], label=m["label"], track_id=tr6["id"])
        if m.get("voices"):
            ctl6.set_mark_voices(ctl6.marks[-1]["id"], m["voices"])
    captured = []
    orig = wt.tk.Menu

    class Capture(orig):
        def __init__(self, *args, **kw):
            super().__init__(*args, **kw)
            captured.append(self)
    wt.tk.Menu = Capture
    try:
        ctl6._show_track_menu(tr6, Event(x_root=0, y_root=0))
    finally:
        wt.tk.Menu = orig
    labels = captured[0].labels()
    check("Export Combined..." in labels and "Export per Voice..." in labels,
          "the track menu offers Export Combined and Export per Voice")
    dlg = wt.VoiceExportDialog(c6, ctl6, tr6, ctl6.track_marks(tr6["id"]))
    check([k for k, v in dlg.vars if v.get()] == ["Lead", "voice 2"], "the dialog checks one track per voice by default")
    path = os.path.join(TMP, "r14-voices.xtiming")
    check(dlg.export(path) and os.path.exists(path), "Export per Voice writes the file")
    import xml.etree.ElementTree as ET
    names = [t.get("name") for t in ET.parse(path).getroot()]
    check(names == ["Lyrics - Lead", "Lyrics - voice 2"], "...one xLights timing track per voice")


def test_round15(th, aa, wt, media):
    print("\n-- round 15: card keys, beats, copy track, renumber, singing faces, pixel editor --")
    import timing_panel as tp

    # card keyboard shortcuts
    ctl, c, _t, tab = bare_controller(wt, fresh_copy(media, "r15_keys"), 100.0)
    tr = ctl._new_track("Lyrics")
    a = ctl._add_mark("range", 1.0, 5.0, label="hello there world", track_id=tr["id"])
    b = ctl._add_mark("range", 5.0, 7.0, label="again", track_id=tr["id"])
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    panel = ctl.panel
    card = panel.cards[a["id"]]
    for seq in ("<Control-Return>", "<Control-space>", "<Control-bracketleft>", "<Control-bracketright>"):
        check(seq in card["text"]._binds if hasattr(card["text"], "_binds") else seq in card["text"].widget._binds,
              f"card text has {seq}")
    card["text"].icursor(len("hello "))
    panel._key_split(a["id"]); run_afters()
    marks = ctl.track_marks(tr["id"])
    check(len(marks) == 3 and marks[0]["label"] == "hello" and marks[1]["label"] == "there world",
          "Ctrl+Enter splits the card at the text cursor")
    second = marks[1]["id"]
    panel.cards[second]["text"].icursor(0)
    check(panel._key_merge(second, -1) == "break" and len(ctl.track_marks(tr["id"])) == 2
          and ctl.mark_by_id(second)["label"] == "hello there world",
          "Backspace at the start of a card merges it with the previous one")
    run_afters()
    f = panel.cards[second]["text"]
    f.icursor(3)
    check(panel._key_merge(second, -1) is None, "...elsewhere Backspace just edits the text")
    f.icursor(len(f.get()))
    panel._key_merge(second, 1); run_afters()
    check(len(ctl.track_marks(tr["id"])) == 1 and "again" in ctl.mark_by_id(second)["label"],
          "Delete at the end merges with the next card")
    ctl.cursor_time = 2.0
    panel.cards[second]["text"].fire("<Control-bracketleft>", Event())
    check(ctl.mark_by_id(second)["start"] == 2.0, "Ctrl+[ sets Start to the @cursor")
    panel._key_play(second, loop=False)
    check(ctl._play_state == "playing" and ctl._play_mark_id == second, "Ctrl+Space plays the card")
    panel._key_play(second, loop=False)
    check(ctl._play_state == "paused", "...and pauses it")
    ctl.stop_play()
    check("Ctrl+Enter" in panel.KEY_HELP and "Ctrl+Space" in panel.KEY_HELP, "the keys are listed for the tooltips/help")

    # Beats: pure helpers
    beats = [round(0.5 * i, 3) for i in range(40)]              # 120 BPM
    strength = [1.0] * 40
    bass = [3.0 if i % 4 == 1 else 0.2 for i in range(40)]      # bar starts at beat index 1
    phase = th.downbeat_phase(strength, bass, 4)
    check(phase == 1, "the bar start is guessed from the bass at each beat")
    all_b = th.beat_marks(beats, 2.0, 6.0, 4, phase, "beats")
    check([m["label"] for m in all_b] == ["4", "1", "2", "3", "4", "1", "2", "3"] and all_b[0]["end"] == 2.5,
          "All beats: beat numbers in the bar, each lasting until the next beat")
    down = th.beat_marks(beats, 0.0, 20.0, 4, phase, "beat", 1)
    check([m["label"] for m in down[:3]] == ["1", "2", "3"] and abs(down[0]["end"] - down[0]["start"] - 0.5) < 1e-9
          and down[0]["start"] == 0.5, "Downbeats: only beat 1, one beat long, labeled with the bar number")
    bars = th.beat_marks(beats, 0.0, 20.0, 4, phase, "bars")
    check([m["label"] for m in bars[:3]] == ["1", "2", "3"] and abs(bars[0]["end"] - bars[0]["start"] - 2.0) < 1e-9,
          "Bars: numbered from 1, each a whole bar")
    check(th.parse_interval("120 bpm") == 0.5 and th.parse_interval("0.25") == 0.25
          and th.parse_interval("500 ms") == 0.5 and th.parse_interval("90") == 60 / 90
          and th.parse_interval("x") is None, "metronome intervals: seconds, ms or BPM")
    met = th.metronome_marks(1.0, 3.0, 0.5, 4)
    check([m["start"] for m in met] == [1.0, 1.5, 2.0, 2.5] and [m["label"] for m in met] == ["1", "2", "3", "4"],
          "metronome ticks from the start, labeled like beats")
    check(th.numbering_cycle(["3", "4", "1", "2", "3"]) == 4 and th.numbering_cycle(["1", "2", "3"]) == 0
          and th.numbering_cycle(["a"]) is None, "Beats tracks count 1..N and wrap; Bars just count up")
    check(th.renumber_from(["1", "2", "3", "4"], 1, 7) == ["1", "7", "8", "9"]
          and th.renumber_from(["1", "2", "3", "4"], 0, 3, cycle=4) == ["3", "4", "1", "2"], "renumbering")
    check(th.unique_track_name("Beats", ["Beats", "Beats 2"]) == "Beats 3", "new track names don't collide")

    # Beats: UI flow with a stand-in detector
    ctl2, c2, _t2, _tab2 = bare_controller(wt, fresh_copy(media, "r15_beats"), 20.0)
    real_avail, real_detect = aa.beats_available, aa.detect_beats
    aa.beats_available = lambda: True
    calls = {"n": 0}

    def fake_detect(path, progress=None):
        calls["n"] += 1
        return {"tempo": 120.0, "beats": beats, "strength": strength, "bass": bass}
    aa.detect_beats = fake_detect
    try:
        wt.set_preference("beats_scope", "cursor")      # Where > From the @cursor to the end
        ctl2.cursor_time = 4.0
        ctl2.run_beats("bars"); run_afters()
        names = [t["name"] for t in ctl2.tracks]
        bars_tr = ctl2.tracks[-1]
        check(names == ["Bars"] and ctl2.track_marks(bars_tr["id"])[0]["start"] >= 4.0,
              "Beats \u25be > Bars makes a \u201cBars\u201d track from the @cursor on")
        ctl2.run_beats("beats"); run_afters()
        check(calls["n"] == 1 and ctl2.tracks[-1]["name"] == "Beats", "...beat detection runs once per file")
        rng = ctl2._add_mark("range", 2.0, 4.0)
        ctl2.selected = ("mark", rng["id"])
        ctl2.run_beats("beat", 3); run_afters()
        m3 = ctl2.track_marks(ctl2.tracks[-1]["id"])
        check(ctl2.tracks[-1]["name"] == "Beat 3" and m3 and all(2.0 <= m["start"] < 4.0 for m in m3),
              "Beat N uses the selected range; the track is named for the choice")
        ctl2.selected = None
        ctl2.cursor_time = 10.0
        met_tr = ctl2.run_metronome("120 bpm")
        check(met_tr["name"] == "Metronome 120 BPM" and ctl2.track_marks(met_tr["id"])[0]["start"] == 10.0,
              "Metronome makes \u201cMetronome 120 BPM\u201d from the @cursor")
        ctl2.beats_menu.entries.clear(); ctl2._fill_beats_menu()
        labels = ctl2.beats_menu.labels()
        check(any(l.startswith("All beats") for l in labels) and any(l.startswith("Bars") for l in labels)
              and "Metronome..." in labels and any(l.startswith("Beats per bar") for l in labels),
              "the Beats \u25be menu lists all beats, downbeats, beat N, bars, metronome, beats per bar")
        bm = ctl2.track_marks(bars_tr["id"])
        ctl2.renumber_from_mark(bm[1]["id"], first=10)
        check([m["label"] for m in sorted(ctl2.track_marks(bars_tr["id"]), key=lambda m: m["start"])][:3]
              == ["1", "10", "11"], "Renumber from Here counts up from the chosen number")
        aa.beats_available = lambda: False
        ctl2.beats_menu.entries.clear(); ctl2._fill_beats_menu()
        check(any("Install" in l for l in ctl2.beats_menu.labels()), "without librosa the menu points to Install")
    finally:
        aa.beats_available, aa.detect_beats = real_avail, real_detect

    # Copy Track
    n_before = len(ctl2.marks)
    copy_tr = ctl2.copy_track(bars_tr)
    check(copy_tr["name"] == "Bars copy" and len(ctl2.track_marks(copy_tr["id"])) == len(ctl2.track_marks(bars_tr["id"]))
          and len(ctl2.marks) == n_before + len(ctl2.track_marks(bars_tr["id"])), "Copy Track duplicates a track")
    ctl2.undo_marks()
    check(ctl2.track_by_id(copy_tr["id"]) is None, "...in one undo step")

    # singing faces
    try:
        from PIL import Image, ImageDraw
    except ImportError:
        print("  (Pillow not installed: face tests skipped)")
        return
    import faces
    img = Image.new("RGB", (100, 100), (230, 190, 160))
    d = ImageDraw.Draw(img)
    for x in (20, 60):
        d.ellipse((x, 30, x + 20, 42), fill="white"); d.ellipse((x + 6, 31, x + 14, 41), fill=(30, 20, 10))
    d.ellipse((35, 65, 65, 77), fill=(180, 60, 70))
    out = faces.generate(img, (15, 25, 85, 47), (30, 60, 70, 82))
    check(len(out) == 20 and set(out) == set(faces.variant_names()), "20 images: 10 mouth shapes x eyes open/closed")
    import numpy as np
    arr = lambda im: np.asarray(im.convert("RGB"), dtype=float)
    mouth = (slice(60, 82), slice(30, 70))
    diffs = {ph: np.abs(arr(out[ph + "_EyesOpen"])[mouth] - arr(img)[mouth]).mean() for ph in faces.PHONEMES}
    check(len({round(v, 1) for v in diffs.values()}) >= 8, "each mouth shape looks different")
    check(np.abs(arr(out["AI_EyesOpen"])[:55] - arr(img)[:55]).mean() < 1.0, "eyes-open images keep the eyes")
    eye = (slice(28, 44), slice(20, 40))
    check(arr(out["AI_EyesClosed"])[eye].min() > 0 and
          (arr(out["AI_EyesClosed"])[eye] > 235).sum() < (arr(img)[eye] > 235).sum() * 0.2,
          "eyes-closed images paint the eye whites over with skin")
    corner = arr(out["rest_EyesOpen"])[90:, 90:]
    check(np.abs(corner - arr(img)[90:, 90:]).max() < 1, "the rest of the picture is untouched")
    path = os.path.join(TMP, "face.png")
    img.save(path)
    folder = faces.save_set(path, out, (15, 25, 85, 47), (30, 60, 70, 82))
    check(len(list(folder.glob("face_*_Eyes*.png"))) == 20 and (folder / "README.txt").exists(),
          "they're saved as face_<shape>_Eyes<Open|Closed>.png with a README")
    check(faces.load_boxes(path) == ((15, 25, 85, 47), (30, 60, 70, 82)) and len(faces.load_set(path)) == 20,
          "the boxes and images load back")
    check(faces.clamp_box((90, 90, 300, 95), (100, 100)) == (90, 90, 100, 95)
          and faces.clamp_box((1, 1, 2, 2), (100, 100)) is None, "boxes are kept inside the image")

    # image tab: viewer + flip + pixel editor (fake Tk)
    import image_tab
    image_tab.messagebox = types.SimpleNamespace(askyesno=lambda *a, **k: True, showinfo=lambda *a, **k: None,
                                                 showerror=lambda *a, **k: None)
    for f_ in folder.glob("*"):
        f_.unlink()
    folder.rmdir()
    canvas = FakeCanvas(FakeWidget())
    viewer = image_tab.ImageViewer(canvas, path)
    check(viewer.kind == "pil" and viewer.variants == {} and viewer.variant_var.get() == "(no faces yet)",
          "a plain image has no faces yet")
    viewer.set_tool("mouth")
    viewer.scale, viewer.cx, viewer.cy, viewer.fit = 1.0, 50.0, 50.0, False
    cw, ch = viewer.canvas_size()
    to_c = lambda x, y: (int(cw / 2 + x - 50), int(ch / 2 + y - 50))
    x0, y0 = to_c(30, 60); x1, y1 = to_c(70, 82)
    viewer._on_press(Event(x=x0, y=y0)); viewer._on_drag(Event(x=x1, y=y1)); viewer._on_release(Event(x=x1, y=y1))
    check(viewer.mouth_box == (30, 60, 70, 82) and viewer.tool is None, "dragging with Mouth \u25ad sets the mouth box")
    viewer.eyes_box = (15, 25, 85, 47)
    check(viewer.make_faces() and len(viewer.variants) == 20 and viewer.view_name == "AI_EyesOpen",
          "Make faces generates, saves and shows the first image")
    viewer.step_variant(1)
    check(viewer.view_name == "AI_EyesClosed" and "eyes closed" in viewer.variant_var.get(), "\u25b6 steps to the next image")
    viewer.step_variant(-1); viewer.step_variant(-1)
    check(viewer.view_name is None and viewer.source is viewer.base, "...and back to the original")
    viewer.toggle_flip()
    for _ in range(3):
        fn = AFTERS.pop() if AFTERS else None
        if fn:
            fn()
    check(viewer.view_name.endswith("_EyesOpen") and "Stop" in viewer.flip_btn._cfg.get("text"),
          "Flip steps through the mouth shapes")
    viewer.toggle_flip()
    check(viewer._flip_id is None, "...until clicked again")
    AFTERS.clear()
    viewer.show_variant("O_EyesOpen")
    viewer.set_tool("pencil")
    viewer.set_color((0, 255, 0))
    viewer.paint_at(5, 5)
    check(viewer.source.getpixel((5, 5))[:3] == (0, 255, 0) and "O_EyesOpen" in viewer._edited,
          "the pixel editor paints the shown image")
    viewer._on_right(Event(x=to_c(50, 50)[0], y=to_c(50, 50)[1]))
    check(viewer.pen_color == tuple(img.getpixel((50, 50))[:3]), "right-click picks a color")
    viewer.undo_pixels()
    check(viewer.variants["O_EyesOpen"].getpixel((5, 5))[:3] == tuple(img.getpixel((5, 5))[:3]),
          "Ctrl+Z undoes the stroke")
    viewer.set_color((0, 255, 0))
    viewer._last_px = None
    viewer.paint_at(6, 6)
    viewer._last_px = None
    saved = viewer.save_edits()
    reread = Image.open(faces.variant_path(path, "O_EyesOpen")).convert("RGB")
    check(saved == ["O_EyesOpen"] and reread.getpixel((6, 6)) == (0, 255, 0),
          f"Save writes the edited image ({saved}, {reread.getpixel((6, 6))})")
    viewer2 = image_tab.ImageViewer(FakeCanvas(FakeWidget()), path)
    check(len(viewer2.variants) == 20 and viewer2.mouth_box == (30, 60, 70, 82),
          "reopening the image finds its faces and boxes")


def test_round16(th, aa, wt, media):
    print("\n-- round 16: shortcuts sheet, overlap filter, tab wrap, Home/End, status bar, shift track --")
    import tracked
    import timing_panel as tp
    src = open(os.path.join(HERE, "tracked.py")).read()
    check('label="Keyboard Shortcuts"' in src and '"<F1>"' in src, "Help > Keyboard Shortcuts (F1)")
    keys = " ".join(k + " " + w for _sec, rows in tracked.SHORTCUTS for k, w in rows)
    for k in ("Ctrl+Enter", "Ctrl+Space", "Home / End", "Ctrl+Play", "Ctrl+Home", "Ctrl+V"):
        check(k in keys, f"the cheat sheet lists {k}")
    app = types.SimpleNamespace(_shortcuts_win=None)
    app.tk = None
    tracked.EditorApp.show_shortcuts(types.SimpleNamespace(**{"_shortcuts_win": None}))
    check(True, "the cheat sheet window builds")
    check("before=self.notebook" in src, "the status bar is packed before the notebook (stays visible when resized)")

    # overlap filter
    marks = [{"id": "a", "type": "range", "start": 0.0, "end": 2.0},
             {"id": "b", "type": "range", "start": 1.5, "end": 3.0},
             {"id": "c", "type": "range", "start": 3.0, "end": 4.0},
             {"id": "d", "type": "point", "start": 3.5},
             {"id": "e", "type": "range", "start": 5.0, "end": 6.0}]
    check(th.overlapping_ids(marks) == {"a", "b", "c", "d"}, "overlapping cards are found (touching ones aren't)")
    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r16"), 100.0)
    tr = ctl._new_track("Lyrics")
    ms = [ctl._add_mark("range", s_, e_, label=f"w{i}", track_id=tr["id"])
          for i, (s_, e_) in enumerate(((1, 2), (2, 3), (2.5, 3.5), (5, 6), (7, 8)))]
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    panel = ctl.panel
    panel.voice_filter_var.set(tp.OVERLAPPING); panel._on_voice_filter(); run_afters()
    check(sorted(panel.cards) == sorted([ms[1]["id"], ms[2]["id"]]), "Show: Overlapping shows only overlapping cards")
    panel.voice_filter_var.set(tp.SHOW_ALL); panel._on_voice_filter(); run_afters()

    # Tab wraps within the track, with the next card scrolled into view too
    seen = []
    real_see = panel._see
    panel._see = lambda mid: seen.append(mid)
    order = list(panel.order)
    panel.focus_adjacent_field(order[-1], "text", 1)
    check(FOCUS["w"] is panel.cards[order[0]]["text"].widget or FOCUS["w"] is panel.cards[order[0]]["text"],
          "Tab on the last card wraps to the first card of the same track")
    check(seen[-1] == order[0] and order[1] in seen, "...and scrolls it and the card after it into view")
    panel.focus_adjacent_field(order[0], "start", -1)
    check(FOCUS["w"] is panel.cards[order[-1]]["start"], "Shift+Tab on the first card wraps to the last")
    seen.clear()
    panel.focus_adjacent_field(order[1], "text", 1)
    check(seen == [order[3], order[2]], "tabbing ahead keeps the target and the next card in view")
    panel.focus_adjacent_field(order[2], "end", 0, absolute=-1)
    check(FOCUS["w"] is panel.cards[order[-1]]["end"], "Ctrl+End goes to the same field of the last card")
    panel._see = real_see
    panel.select_end_card(last=True)
    check(ctl.selected == ("mark", order[-1]), "End in the card list selects the last card")
    panel.select_end_card(last=False)
    check(ctl.selected == ("mark", order[0]), "Home selects the first")

    # Home / End on the waveform
    ctl.selected = ("mark", ms[2]["id"])
    ctl.select_end_mark(last=True)
    check(ctl.selected == ("mark", ms[4]["id"]), "End on the waveform: last mark of the track")
    ctl.select_end_mark(last=False)
    check(ctl.selected == ("mark", ms[0]["id"]), "Home: first mark of the track")
    check("<Home>" in c._binds and "<End>" in c._binds, "Home/End are bound on the waveform")

    # Shift track
    done = ctl.shift_track(tr, 0.5)
    check(done == 0.5 and ctl.mark_by_id(ms[0]["id"])["start"] == 1.5 and ctl.mark_by_id(ms[4]["id"])["end"] == 8.5,
          "Shift Track moves every mark of the track")
    done = ctl.shift_track(tr, -5.0)
    check(abs(done + 1.5) < 1e-9 and ctl.mark_by_id(ms[0]["id"])["start"] == 0.0,
          "...but not before 0:00 (limited, lengths kept)")
    ctl.undo_marks()
    check(ctl.mark_by_id(ms[0]["id"])["start"] == 1.5, "...one undo step each")
    wt.simpledialog.askstring = lambda *a, **k: "-0.25"
    try:
        ctl.ask_shift_track(tr)
    finally:
        wt.simpledialog.askstring = lambda *a, **k: None
    check(ctl.mark_by_id(ms[0]["id"])["start"] == 1.25, "Shift Track... asks for the seconds")


def test_round17(th, aa, wt, media):
    print("\n-- round 17: filter menu/note, current tab, sidecar backups, updates, image panel, launch logs --")
    import tracked
    import timing_panel as tp
    import updater
    import io, zipfile

    # Show: menu groups + empty note
    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r17"), 100.0)
    tr = ctl._new_track("Lyrics")
    a = ctl._add_mark("range", 1.0, 2.0, label="a", track_id=tr["id"])
    ctl.set_mark_voices(a["id"], ["Lead"])
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    panel = ctl.panel
    menu = FakeMenu()
    panel._fill_filter_menu(menu)
    kinds = [e.get("kind") for e in menu.entries]
    check(kinds.count("separator") == 3 and [e["label"] for e in menu.entries if e.get("label")]
          == ["All cards", "Lead", "All voices", "Overlapping"],
          "Show: lists All cards | voices | All voices | Overlapping, with separators between the groups")
    panel.voice_filter_var.set(tp.OVERLAPPING); panel._on_voice_filter(); run_afters()
    check("overlap another card" in panel.empty_note() and "no marks in this track yet" not in panel.empty_note(),
          "with a filter on, an empty list says which filter hides the cards")
    panel.voice_filter_var.set("Lead")
    check("are for Lead" in panel.empty_note(), "...naming the voice")
    panel.voice_filter_var.set(tp.SHOW_ALL)
    tr2 = ctl._new_track("Empty")
    ctl.selected = ("track", tr2["id"]); ctl.render_waveform(); run_afters()
    check("no marks in this track yet" in panel.empty_note(), "an empty track still says it has no marks")

    # current tab survives the quit questions
    class ET:
        def __init__(self, n):
            self.filepath = f"/x/{n}"

        def save_current_sash(self):
            pass

        def save_cursor_state(self):
            pass
    tabs = [ET(n) for n in "abc"]
    fake = types.SimpleNamespace(tabs=tabs, current_tab=lambda: tabs[2])
    real_load, real_et, real_recent = tracked.load_session_data, tracked.EditorTab, tracked.load_recent
    tracked.load_session_data, tracked.EditorTab, tracked.load_recent = (lambda: {}), ET, (lambda: [])
    try:
        data = tracked.EditorApp._collect_session(fake, active=tabs[1])
    finally:
        tracked.load_session_data, tracked.EditorTab, tracked.load_recent = real_load, real_et, real_recent
    check(data["active_index"] == 1, "the session remembers the tab that was current before quitting")
    src = open(os.path.join(HERE, "tracked.py")).read()
    check("active = self.current_tab()" in src and "_collect_session(active=active)" in src,
          "on_quit takes the current tab before its questions select other tabs")

    # sidecar backups
    side = os.path.join(TMP, "bak-tracked.json")
    open(side, "w").write("{}")
    first = th.backup_sidecar(side, stamp="20260101-000000")
    second = th.backup_sidecar(side, stamp="20260102-000000")
    import glob as _g
    baks = _g.glob(os.path.join(TMP, "bak-tracked-*.json"))
    check(first.endswith("bak-tracked-20260101-000000.json") and baks == [second],
          "a timestamped backup (song-tracked-<date>-<time>.json); only the newest is kept")
    check(th.backup_sidecar(os.path.join(TMP, "none.json")) is None, "no sidecar, no backup")
    song = fresh_copy(media, "r17_bak")
    open(th.cache_path(song), "w").write("{}")
    wt.set_preference("backup_sidecars", True)
    try:
        wt._BACKED_UP.clear()
        made = wt.backup_sidecar_once(song)
        again = wt.backup_sidecar_once(song)
    finally:
        wt.set_preference("backup_sidecars", False)
    check(made and again is None, "with the preference on, each sidecar is backed up once per run (at startup)")
    wt._BACKED_UP.clear()
    check(wt.backup_sidecar_once(song) is None, "...and not at all when it's off")

    # updates
    check(updater.is_newer("1.10.0", "1.9.3") and not updater.is_newer("1.2.0", "1.2")
          and updater.is_newer("2", "1.99.99"), "version comparison is numeric")
    check(updater.valid_repo("someone/trackED") and not updater.valid_repo("not a repo"), "repo names are checked")
    check(updater.remote_version("o/r", fetch=lambda url: b'x = 1\nVERSION = "1.4.2"\n') == "1.4.2",
          "the repository's version is read from its tracked.py")
    app_dir = os.path.join(TMP, "upd_app"); os.makedirs(app_dir, exist_ok=True)
    open(os.path.join(app_dir, "a.py"), "w").write("old")
    open(os.path.join(app_dir, "same.txt"), "w").write("same")
    open(os.path.join(app_dir, "mine.txt"), "w").write("keep")
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w") as zf:
        zf.writestr("trackED-main/a.py", "new")
        zf.writestr("trackED-main/same.txt", "same")
        zf.writestr("trackED-main/sub/b.md", "doc")
        zf.writestr("trackED-main/.git/config", "x")
        zf.writestr("trackED-main/../evil.py", "x")
    changed, backup = updater.apply_zip(buf.getvalue(), app_dir, backup_root=os.path.join(TMP, "upd_bak"))
    check(sorted(changed) == ["a.py", "sub/b.md"] and open(os.path.join(app_dir, "a.py")).read() == "new"
          and open(os.path.join(app_dir, "mine.txt")).read() == "keep",
          "updating writes changed files only and leaves the user's other files")
    check(backup and open(os.path.join(backup, "a.py")).read() == "old", "...after backing up what it replaces")
    check(not os.path.exists(os.path.join(TMP, "evil.py")), "...and never writes outside the app folder")
    check(updater.needs_restart(changed) and not updater.needs_restart(["sub/b.md"]), "a restart is offered for .py changes")

    # image panel grows when zooming in (up to 75% of the window)
    try:
        from PIL import Image
    except ImportError:
        Image = None
    import image_tab
    if Image is not None:
        path = os.path.join(TMP, "tall.png")
        Image.new("RGB", (100, 400), (10, 20, 30)).save(path)
        sash = {"pos": 200}
        paned = types.SimpleNamespace(sashpos=lambda i, v=None: sash.update(pos=v) if v is not None else sash["pos"],
                                      winfo_height=lambda: 900)
        tab = types.SimpleNamespace(paned=paned)
        canvas = FakeCanvas(FakeWidget())
        canvas.winfo_toplevel = lambda: types.SimpleNamespace(winfo_height=lambda: 1000)
        viewer = image_tab.ImageViewer(canvas, path, tab=tab)
        viewer.set_scale(1.0)
        grew_to = sash["pos"]
        viewer.set_scale(4.0)
        check(grew_to > 200 and sash["pos"] == 750, "zooming in grows the image panel, up to 75% of the window")
        sash["pos"] = 800
        viewer.set_scale(0.5)
        check(sash["pos"] == 800, "...and never shrinks it")
    real = image_tab._pillow_installed
    image_tab._pillow_installed = lambda: False
    try:
        jpg = os.path.join(TMP, "x.jpg")
        open(jpg, "wb").write(b"not really")
        v = image_tab.ImageViewer.__new__(image_tab.ImageViewer)
        v.canvas, v.kind, v.source, v.image_size = FakeCanvas(FakeWidget()), None, None, (0, 0)
        v.canvas._plugin_toolbars = []
        v._build_toolbar()
        check(getattr(v, "install_btn", None) is not None and "Install" in v.install_btn._cfg.get("text", ""),
              "the image tab shows an \u26a0 Install button when Pillow is missing")
    finally:
        image_tab._pillow_installed = real

    # launch diagnostics
    real_out, real_err = sys.stdout, sys.stderr
    home = os.environ.get("HOME")
    os.environ["HOME"] = TMP
    try:
        sys.stderr = None
        log = tracked.capture_output_if_windowless()
        sys.stderr.write("boom\n")
        sys.stderr.flush()
    finally:
        sys.stdout, sys.stderr = real_out, real_err
        if home is not None:
            os.environ["HOME"] = home
    check(log and "boom" in open(log).read(), "without a console (pythonw), errors go to ~/.tracked/console.log")
    cmd = open(os.path.join(HERE, "trackED.cmd"), newline="").read()
    check("--check" in cmd and "--console" in cmd and "\r\n" in cmd, "trackED.cmd has --check / --console (CRLF kept)")


def test_round18(th, aa, wt, media):
    print("\n-- round 18: install progress, image backdrop/overlay, Faces menu, flip order --")
    import deps
    # deps.install: one package at a time, with start/ok/failed steps
    steps = []
    real_run = deps._run
    deps._run = lambda cmd, log, timeout=3600: (0 if "librosa" in cmd else 1, "error")
    try:
        ok, failed = deps.install(["librosa", "demucs"], on_step=lambda k, st: steps.append((k, st)))
    finally:
        deps._run = real_run
    check(steps == [("librosa", "start"), ("librosa", "ok"), ("demucs", "start"), ("demucs", "failed")]
          and ok == ["librosa"] and [k for k, _ in failed] == ["demucs"],
          "packages install one at a time, reporting start / ok / failed for each")

    # the dialog: highlight while installing, then the result + Restart in the window
    canvas = FakeCanvas(FakeWidget())
    real_missing = deps.missing
    deps.missing = lambda include_broken=False: [deps.BY_KEY["librosa"], deps.BY_KEY["demucs"]]
    restarts = []
    try:
        dlg = wt.InstallDialog(canvas, restart=lambda: restarts.append(1))
    finally:
        deps.missing = real_missing
    dlg._row_state("librosa", "start")
    check(all(w._cfg.get("bg") == wt.DLG_BUSY_BG for w in dlg.rows["librosa"])
          and dlg.rows["librosa"][3]._cfg.get("text") == "installing...",
          "the package being installed is highlighted")
    dlg._row_state("librosa", "ok")
    check(dlg.rows["librosa"][0]._cfg.get("bg") == wt.DLG_BG and "\u2713" in dlg.rows["librosa"][3]._cfg["text"]
          and dlg.vars["librosa"].get() is False and dlg.rows["librosa"][0]._cfg.get("state") == "disabled",
          "...then marked \u2713 installed (unchecked, no longer selectable)")
    dlg._row_state("demucs", "failed")
    check("\u2717" in dlg.rows["demucs"][3]._cfg["text"], "a failed one is marked \u2717")
    dlg._finished(["librosa"], [("demucs", "x")])
    check("Installed: librosa" in dlg.header._cfg["text"] and "Restart" in dlg.header._cfg["text"]
          and dlg.restart_btn.packed, "the window itself says what was installed and offers Restart")
    dlg.restart_btn._cfg["command"]()
    check(restarts == [1], "...which restarts trackED")

    try:
        from PIL import Image
    except ImportError:
        return
    import image_tab, faces
    path = os.path.join(TMP, "r18.png")
    img = Image.new("RGBA", (20, 20), (200, 150, 120, 255))
    img.putpixel((3, 4), (10, 20, 30, 128))
    img.save(path)
    canvas = FakeCanvas(FakeWidget())
    v = image_tab.ImageViewer(canvas, path)
    v.fit, v.scale, v.cx, v.cy = False, 10.0, 10.0, 10.0
    v.redraw()
    tags = [it.get("tags") for it in canvas.items] if hasattr(canvas, "items") else []
    bg_lines = canvas.find_withtag("plugin_bg") if hasattr(canvas, "find_withtag") else []
    check(v.BACKDROP and callable(v._draw_backdrop), "a light gray grid is drawn behind the image")
    xs, ys = v._grid_lines(1, 0, 0, 400, 300)
    check(len(xs) > 10 and abs((xs[1] - xs[0]) - 10.0) < 1e-6, "...its lines fall on the image's pixel boundaries")
    v.scale = 0.5
    step = 1
    while step * v.scale < 8:
        step *= 2
    check(step == 16, "...every few pixels when zoomed out (lines at least 8 px apart)")
    v.scale = 10.0
    cw, ch = v.canvas_size()
    x, y = v.to_canvas(3.5, 4.5)
    v._on_motion(Event(x=x, y=y))
    check(v.coords_text().startswith("x 3  y 4  #0a141e") and "a128" in v.coords_text(),
          "the pointer's pixel coordinates (and color) show along the bottom")
    v._on_leave()
    check(v.coords_text() == "", "...and clear when the pointer leaves")
    v.set_tool("pencil")
    check("Pixel editor on" in v.status_msg, "messages show along the bottom of the image area (not cut off)")
    labels = v.faces_menu.labels() if hasattr(v.faces_menu, "labels") else [e.get("label") for e in v.faces_menu.entries]
    check(any(l.startswith("Mark eyes") for l in labels) and any(l.startswith("Mark mouth") for l in labels)
          and "Make faces" in labels, "Faces \u25be holds Mark eyes, Mark mouth and Make faces")
    image_tab.messagebox = types.SimpleNamespace(askyesno=lambda *a, **k: True, showinfo=lambda *a, **k: None,
                                                 showerror=lambda *a, **k: None)
    v.set_tool(None)
    v.mouth_box, v.eyes_box = (5, 12, 15, 18), (3, 3, 17, 9)
    v.make_faces(confirm=False)
    check(v.view_name is not None, "after Make faces a face image is shown")
    v.mark("eyes")
    check(v.view_name is None and v.tool == "eyes", "Mark eyes again goes back to the original, where the boxes show")
    v.toggle_flip()
    seen = []
    for _ in range(len(v.variants)):
        fn = AFTERS.pop() if AFTERS else None
        seen.append(v.view_name)
        if fn:
            fn()
    v.toggle_flip(); AFTERS.clear()
    n_open = len([n for n in v.variants if n.endswith("_EyesOpen")])
    check(all(n.endswith("_EyesOpen") for n in seen[:n_open]) and all(n.endswith("_EyesClosed") for n in seen[n_open:]),
          "Flip shows the eyes-open images first, then the eyes-closed ones")
    import shutil as _sh
    _sh.rmtree(faces.faces_dir(path), ignore_errors=True)


def test_round19(th, aa, wt, media):
    print("\n-- round 19: reversible merges (Unmerge), default update repo, Auto-browse --")
    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r19"), 100.0)
    tr = ctl._new_track("Lyrics")
    specs = [(1.0, 2.0, "one"), (2.2, 3.0, "two"), (3.0, 4.5, "three four")]
    ms = [ctl._add_mark("range", a, b, label=t, track_id=tr["id"]) for a, b, t in specs]
    ctl.set_mark_voices(ms[1]["id"], ["Lead"])
    ctl.merge_mark_by_id(ms[0]["id"], 1)
    ctl.merge_mark_by_id(ms[0]["id"], 1)
    merged = ctl.mark_by_id(ms[0]["id"])
    check(len(ctl.track_marks(tr["id"])) == 1 and len(merged["pieces"]) == 3,
          "a merged card remembers the cards it was made of (merges of merges too)")
    ctl._add_mark("point", 50.0, None)                      # other work in between: not an undo
    n, how = ctl.unmerge_mark_by_id(ms[0]["id"])
    back = sorted(ctl.track_marks(tr["id"]), key=lambda m: m["start"])
    check(n == 3 and how == "exact" and [(m["start"], m["end"], m["label"]) for m in back] == specs,
          "Unmerge brings back the original cards with their own start/end times and text")
    check(back[1].get("voices") == ["Lead"] and "pieces" not in back[0], "...and their voices")
    check(len(ctl.marks) == 4, "...without undoing the other edits made since")
    # merge, then move + edit text, then unmerge
    ctl.merge_mark_by_id(back[0]["id"], 1)
    m = ctl.mark_by_id(back[0]["id"])
    m["start"], m["end"] = 11.0, 13.0                      # was 1.0 .. 3.0, now 2 s long from 11 s
    m["label"] = "uno dos"
    n, how = ctl.unmerge_mark_by_id(m["id"])
    parts = sorted((x for x in ctl.track_marks(tr["id"]) if x["start"] >= 11.0), key=lambda x: x["start"])
    check(how == "moved+text" and [(p["start"], p["end"]) for p in parts] == [(11.0, 12.0), (12.2, 13.0)]
          and [p["label"] for p in parts] == ["uno", "dos"],
          "after the card was moved/resized, the original boundaries are fitted into its new span")
    plan, how = th.unmerge_plan({"start": 0.0, "end": 2.0, "label": "a b c",
                                 "pieces": [{"start": 0.0, "end": 1.0, "label": "x"},
                                            {"start": 1.0, "end": 2.0, "label": "y"}]})
    check(how == "text" and [p["label"] for p in plan] == ["a", "b c"] or [p["label"] for p in plan] == ["a b", "c"],
          "edited text with a different word count is shared out in proportion")
    check(th.unmerge_plan({"start": 0, "end": 1, "label": "x"}) == ([], ""), "a card that wasn't merged has no plan")
    # a merged card split by hand keeps the pieces on each side
    a2 = ctl._add_mark("range", 20.0, 21.0, label="aa", track_id=tr["id"])
    b2 = ctl._add_mark("range", 21.0, 22.0, label="bb", track_id=tr["id"])
    c2 = ctl._add_mark("range", 22.0, 23.0, label="cc", track_id=tr["id"])
    d2 = ctl._add_mark("range", 23.0, 24.0, label="dd", track_id=tr["id"])
    for _ in range(3):
        ctl.merge_mark_by_id(a2["id"], 1)
    ctl.split_mark_by_id(a2["id"], at_time=22.0)
    left = ctl.mark_by_id(a2["id"])
    right = next(m for m in ctl.track_marks(tr["id"]) if m["start"] == 22.0)
    check(len(left["pieces"]) == 2 and len(right["pieces"]) == 2, "splitting a merged card shares its pieces out")
    ctl.unmerge_mark_by_id(right["id"])
    check(sorted(m["label"] for m in ctl.track_marks(tr["id"]) if m["start"] >= 22.0) == ["cc", "dd"],
          "...so each part can still be unmerged")
    # the menus offer it
    ctl.selected = ("track", tr["id"]); ctl.render_waveform(); run_afters()
    menu = FakeMenu()
    ctl.panel._split_ctx = None
    if hasattr(ctl.panel, "_fill_split_menu"):
        ctl.panel._fill_split_menu(left["id"], menu)
        check(any(l.startswith("Unmerge into the 2") for l in menu.labels()), "Split \u25be offers Unmerge")
    ctl.mark_by_id(a2["id"])["pieces"] and ctl.unmerge_mark_by_id(a2["id"])
    ctl.undo_marks()
    check(len(ctl.mark_by_id(a2["id"]).get("pieces") or []) == 2, "Unmerge is one undo step")
    th.save_marks(ctl.filepath, ctl.marks, ctl.tracks, ctl.voices)
    saved = th.load_cache(ctl.filepath)["marks"]
    check(any(len(m.get("pieces") or []) == 2 for m in saved), "the remembered pieces are saved with the marks")

    # default update repo
    import updater
    app = os.path.join(TMP, "gitclone"); os.makedirs(os.path.join(app, ".git"), exist_ok=True)
    open(os.path.join(app, ".git", "config"), "w").write(
        '[core]\n\tbare = false\n[remote "origin"]\n\turl = git@github.com:someone/trackED.git\n')
    check(updater.repo_from_git(app) == "someone/trackED", "a git clone finds its GitHub repository by itself")
    check(updater.default_repo("me/fork", app) == "me/fork", "the Preferences setting wins")
    real = updater.UPDATE_REPO
    updater.UPDATE_REPO = "official/trackED"
    try:
        check(updater.default_repo("", os.path.join(TMP, "nogit")) == "official/trackED",
              "otherwise the UPDATE_REPO constant")
    finally:
        updater.UPDATE_REPO = real
    src = open(os.path.join(HERE, "image_tab.py")).read()
    check("Auto-browse" in src and '"Flip"' not in src, "the image tab's Flip button is now \u25b6 Auto-browse")


def test_round20(th, aa, wt, media):
    print("\n-- round 20: unmerge after copy/clear, shift to @cursor, selection menu, group restore, @ Ctrl+click --")
    ctl, c, _t, tab = bare_controller(wt, fresh_copy(media, "r20"), 100.0)
    tr = ctl._new_track("Lyrics")
    specs = [(1.0, 2.0, "one"), (2.0, 3.0, "two"), (3.0, 4.0, "three")]
    ms = [ctl._add_mark("range", a, b, label=t, track_id=tr["id"]) for a, b, t in specs]
    ctl.merge_mark_by_id(ms[0]["id"], 1); ctl.merge_mark_by_id(ms[0]["id"], 1)
    merged = ctl.mark_by_id(ms[0]["id"])
    # Copy to a new track, then unmerge there
    ctl.selected = ("mark", merged["id"]); ctl._multi = []
    copies = ctl.move_selection_to_track(ctl._new_track("Copy", record_history=False)["id"], [merged["id"]], keep=True)
    n, how = ctl.unmerge_mark_by_id(copies[0]["id"])
    got = sorted((m["start"], m["end"], m["label"]) for m in ctl.marks if m.get("track_id") == copies[0]["track_id"])
    check(n == 3 and how == "exact" and got == specs, "a copied merged card unmerges into the original times")
    # pasted at the @cursor: the originals move with it
    ctl.copy_selection([merged["id"]])
    ctl.cursor_time = 50.0
    pasted = ctl.paste_marks(tr["id"], at_cursor=True)
    n, how = ctl.unmerge_mark_by_id(pasted[0]["id"])
    got = sorted((m["start"], m["end"]) for m in ctl.marks if m["start"] >= 50.0)
    check(how == "exact" and got == [(50.0, 51.0), (51.0, 52.0), (52.0, 53.0)], "...also when pasted elsewhere")
    # End cleared / set onto Start: originals keep their lengths (not all on one instant)
    merged["end"] = None; merged["type"] = "point"
    plan, how = th.unmerge_plan(merged)
    check([(p["start"], p["end"]) for p in plan] == [(1.0, 2.0), (2.0, 3.0), (3.0, 4.0)],
          "a merged card whose End was cleared doesn't collapse its cards onto one time")
    merged["end"] = 1.0; merged["type"] = "range"
    plan, _ = th.unmerge_plan(merged)
    check(len({p["start"] for p in plan}) == 3, "...nor one whose End was set onto its Start")
    merged["end"] = 4.0

    # shift the selection so the first selected mark starts at the @cursor
    ctl2, c2, _t2, _tab2 = bare_controller(wt, fresh_copy(media, "r20b"), 100.0)
    t2 = ctl2._new_track("T")
    xs = [ctl2._add_mark("range", float(s_), s_ + 0.5, label=str(s_), track_id=t2["id"]) for s_ in (2, 4, 6, 8)]
    ctl2.selected = ("mark", xs[2]["id"]); ctl2._multi = [xs[1]["id"], xs[2]["id"]]
    ctl2.cursor_time = 10.0
    ctl2.shift_selection_to_cursor()
    check(ctl2.mark_by_id(xs[1]["id"])["start"] == 10.0 and ctl2.mark_by_id(xs[2]["id"])["start"] == 12.0
          and ctl2.mark_by_id(xs[0]["id"])["start"] == 2.0, "Shift to @cursor: the first selected starts there, the rest follow")
    ctl2.undo_marks()
    ctl2.cursor_time = 3.0
    ctl2.shift_track_to_cursor(t2)
    check([ctl2.mark_by_id(x["id"])["start"] for x in xs] == [1.0, 3.0, 5.0, 7.0],
          "Shift Track to @cursor: the whole track moves so its first selected mark starts there")
    check(ctl2.shift_marks([xs[0]["id"]], -50.0) == -1.0 and ctl2.mark_by_id(xs[0]["id"])["start"] == 0.0,
          "shifts stop at 0:00")
    captured = []
    orig = wt.tk.Menu

    class Capture(orig):
        def __init__(self, *a, **k):
            super().__init__(*a, **k)
            captured.append(self)
    wt.tk.Menu = Capture
    try:
        ctl2.selected = ("mark", xs[2]["id"]); ctl2._multi = [xs[1]["id"], xs[2]["id"]]
        ctl2.show_selection_menu(Event(x_root=0, y_root=0))
        labels = captured[0].labels()
        captured.clear()
        ctl2._show_track_menu(t2, Event(x_root=0, y_root=0))
        tlabels = captured[0].labels()
    finally:
        wt.tk.Menu = orig
    check(any(l.startswith("Shift 2 Marks to @cursor") for l in labels) and "Shift 2 Marks..." in labels
          and "Move 2 Marks to Track" in labels and "Delete 2 Marks" in labels,
          "right-clicking selected cards offers shift / cut / copy / move / delete for all of them")
    check(any(l.startswith("Shift Track to @cursor") for l in tlabels) and any(l.startswith("Shift 2 Marks") for l in tlabels),
          "the track menu offers Shift Track to @cursor and shifting the selected marks")

    # the card editor: Ctrl+click selects more cards, right-click shows that menu
    ctl2.selected = ("track", t2["id"]); ctl2._multi = []; ctl2.render_waveform(); run_afters()
    panel = ctl2.panel
    ctl2.select_mark(xs[0]["id"], from_panel=True)
    panel._extend(xs[3]["id"], toggle=True)
    check(set(ctl2.selected_mark_ids()) == {xs[0]["id"], xs[3]["id"]}, "Ctrl+click on cards selects several")
    shown = []
    real = ctl2.show_selection_menu
    ctl2.show_selection_menu = lambda ev, ids=None: shown.append(list(ctl2.selected_mark_ids()))
    panel._card_menu(xs[3]["id"], Event(x_root=0, y_root=0))
    panel._card_menu(xs[1]["id"], Event(x_root=0, y_root=0))
    ctl2.show_selection_menu = real
    check(len(shown[0]) == 2 and shown[1] == [xs[1]["id"]],
          "right-click on a selected card: menu for the group; on another card: for it alone")

    # several selected cards are remembered for the next start
    ctl2.select_mark(xs[0]["id"], from_panel=True)
    panel._extend(xs[2]["id"], toggle=False)
    group = list(ctl2.selected_mark_ids())
    ctl2.save_marks_now()
    ctl2.remember_selection()
    ctl3, _c3, _t3, _tab3 = bare_controller(wt, ctl2.filepath, 100.0)
    ctl3._restore_selection(reveal=False)
    check(len(group) == 3 and ctl3.selected_mark_ids() == group, "all the selected cards are selected again after a restart")

    # Ctrl+click on a card's @: the @cursor goes to its Start / End
    card = panel.cards[xs[1]["id"]]
    check("<Control-Button-1>" in card["end_at"]._binds, "Ctrl+click on @ is bound")
    panel._cursor_to(xs[1]["id"], "end")
    check(abs(ctl2.cursor_time - ctl2.mark_by_id(xs[1]["id"])["end"]) < 1e-9, "Ctrl+click on End's @ puts the @cursor there")
    panel._cursor_to(xs[1]["id"], "start")
    check(abs(ctl2.cursor_time - ctl2.mark_by_id(xs[1]["id"])["start"]) < 1e-9, "...and on Start's @ at the start")

    # a new track gets room
    sash = {"pos": 200}
    ctl2.tab = types.SimpleNamespace(paned=types.SimpleNamespace(
        sashpos=lambda i, v=None: sash.update(pos=v) if v is not None else sash["pos"]), mark_dirty=lambda: None)
    c2.winfo_height = lambda: 120
    c2.winfo_toplevel = lambda: types.SimpleNamespace(winfo_height=lambda: 1000)
    for k in range(4):
        ctl2._new_track(f"extra {k}", record_history=False)
    ctl2._ensure_tracks_fit()
    need = 60 + ctl2.STATUS_ROW_HEIGHT + len(ctl2.tracks) * ctl2.TRACK_HEIGHT + 4
    check(sash["pos"] == 200 + need - 120, "a new track grows the waveform panel so every band is visible")


def test_round21(th, aa, wt, media):
    print("\n-- round 21: user action log, backup names, debug.log last, Beats messages --")
    import tracked
    # backup names
    check(th.backup_name("/m/song-tracked.json", "20261003-141500") == "/m/song-tracked-20261003-141500.json",
          "backups are named song-tracked-20261003-141500.json")
    other = os.path.join(TMP, "keep-tracked.json"); open(other, "w").write("{}")
    th.backup_sidecar(os.path.join(TMP, "bak-tracked.json"), stamp="20260103-000000")
    check(os.path.exists(other), "...and cleaning up old backups touches nothing else")

    # user action log
    logged = []
    real_debug = tracked.debug
    tracked.debug = lambda level, msg, **k: logged.append((level, msg))
    tracked.LOG_ACTIONS_CLI["on"] = True
    try:
        root = FakeWidget()
        root.after = lambda ms, fn: AFTERS.append(fn) or len(AFTERS)
        root.after_cancel = lambda i: None
        class_binds = []
        root.bind_class = lambda cls, seq, fn, add=None: class_binds.append((cls, seq, add))
        log = tracked.UserActionLog(root)
        # Tk's menu.tcl binds these on the Menu class; a more specific
        # sequence (e.g. <ButtonRelease-1>) would replace Tk's and menus
        # would stop working -- so only these exact sequences, appended.
        tk_menu_class_seqs = {"<ButtonRelease>", "<KeyPress-Return>", "<<MenuSelect>>"}
        check(all(cls == "Menu" and seq in tk_menu_class_seqs and add == "+" for cls, seq, add in class_binds)
              and ("Menu", "<ButtonRelease>", "+") in class_binds,
              "the action log adds to Tk's own Menu bindings instead of replacing them (menu items keep working)")

        class W:
            def __init__(self, cls, text="", path=".tab.card.start"):
                self._cls, self._text, self._path = cls, text, path

            def winfo_class(self):
                return self._cls

            def cget(self, k):
                return self._text

            def __str__(self):
                return self._path
        entry, btn, canvas = W("Entry"), W("Button", "Save"), W("Canvas", path=".tab.waveform")
        for ch in "hi":
            log.on_key(types.SimpleNamespace(char=ch, keysym=ch, state=0, widget=entry))
        log.on_key(types.SimpleNamespace(char="\x13", keysym="s", state=0x0004, widget=entry))
        log.on_button(types.SimpleNamespace(num=1, state=0, widget=btn, x=1, y=2))
        log.on_button(types.SimpleNamespace(num=3, state=0x0004, widget=canvas, x=10, y=20))
        log.on_key(types.SimpleNamespace(char="", keysym="Shift_L", state=0, widget=entry))
        log._menu_label = "Copy Track"
        log.on_menu_pick(types.SimpleNamespace(widget=None))
        lines = [m for lv, m in logged]
        check(all(lv == tracked.USER_ACTION_LEVEL for lv, _ in logged) and all(m.startswith("ACTION ") for m in lines),
              "user actions go to the debug log as ACTION lines at their own level")
        check(lines[0] == "ACTION typed 'hi' in Entry (card.start)", "typing is gathered into one line per field")
        check(lines[1] == "ACTION key Ctrl+s in Entry (card.start)", "keys with modifiers are named")
        check(lines[2] == "ACTION click on Button 'Save'", "clicks name the button")
        check(lines[3] == "ACTION Ctrl+right-click on Canvas (tab.waveform) at 10,20", "...and where on a canvas")
        check(lines[4] == "ACTION menu pick 'Copy Track'" and len(lines) == 5,
              "menu picks are logged; lone modifier keys aren't")
        tracked.LOG_ACTIONS_CLI["on"] = False
        logged.clear()
        log.on_button(types.SimpleNamespace(num=1, state=0, widget=btn, x=0, y=0))
        check(logged == [], "nothing is logged while the setting is off")
    finally:
        tracked.debug = real_debug
        tracked.LOG_ACTIONS_CLI["on"] = None
    check(tracked.parse_args(["t.py", "-actions"]) is not None and tracked.LOG_ACTIONS_CLI["on"] is True,
          "-actions turns it on for one run")
    tracked.LOG_ACTIONS_CLI["on"] = None

    # debug.log opened as a file is kept right-most
    log_path = str(tracked.debug_log_path())
    a, b = types.SimpleNamespace(filepath="/x/a.txt", frame="f_a"), types.SimpleNamespace(filepath=log_path, frame="f_log")
    c_ = types.SimpleNamespace(filepath="/x/c.txt", frame="f_c")
    order = ["f_a", "f_log", "f_c"]
    nb = types.SimpleNamespace(tabs=lambda: list(order),
                               insert=lambda where, child: (order.remove(child), order.append(child)))
    app = types.SimpleNamespace(tabs=[a, b, c_], notebook=nb, _debug_tab=None)
    app._debug_log_tab = lambda: tracked.EditorApp._debug_log_tab(app)
    tracked.EditorApp._keep_debug_last(app)
    check(order[-1] == "f_log" and app.tabs[-1] is b, "debug.log opened as a file is moved to the right-most tab")

    # Beats: a range with no beat says why
    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r21"), 20.0)
    infos = []
    ctl.append_info = lambda t: infos.append(t)
    rng = ctl._add_mark("range", 5.1, 5.3, label="short card")
    ctl.selected = ("mark", rng["id"])
    ctl._beat_range_why = ctl.analysis_range_why()[2]
    beats = [0.5 * i for i in range(40)]
    out = ctl._make_beat_track({"beats": beats, "strength": [1.0] * 40, "bass": [1.0] * 40, "tempo": 120.0},
                               "beat", 1, 5.1, 5.3)
    check(out is None and "No track made" in infos[-1] and "the selected range" in infos[-1]
          and "Esc" in infos[-1], "when no track can be made, the panel says which range was used and why")


def test_round22(th, aa, wt, media):
    print("\n-- round 22: export folder/confirm/status, card actions in the mark menus --")
    from pathlib import Path
    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r22"), 100.0)
    tr = ctl._new_track("Lyrics")
    ms = [ctl._add_mark("range", float(i), i + 1.0, label=f"w{i} x{i}", track_id=tr["id"]) for i in range(1, 5)]
    seen = {}
    out = os.path.join(TMP, "r22-out.xtiming")
    real = wt.filedialog.asksaveasfilename
    wt.filedialog.asksaveasfilename = lambda **k: (seen.update(k), out)[1]
    try:
        ok = ctl.export_timing_track(tr)
    finally:
        wt.filedialog.asksaveasfilename = real
    check(seen.get("initialdir") == str(Path(ctl.filepath).resolve().parent) and seen.get("confirmoverwrite") is True,
          "exports open in the audio file's folder and ask before replacing a file")
    check(ok and os.path.exists(out) and "Exported 1 timing track to r22-out.xtiming" in ctl.play_status_var.get(),
          "a successful export says so in the status bar")
    statuses = []
    c.winfo_toplevel = lambda: types.SimpleNamespace(set_status=lambda m: statuses.append(m))
    ctl.announce("hello")
    check(statuses == ["hello"], "...the app's status bar, too")

    captured = []
    orig = wt.tk.Menu

    class Capture(orig):
        def __init__(self, *a, **k):
            super().__init__(*a, **k)
            captured.append(self)
    wt.tk.Menu = Capture
    try:
        ctl.selected = ("mark", ms[1]["id"]); ctl._multi = [ms[1]["id"], ms[2]["id"]]
        ctl.show_selection_menu(Event(x_root=0, y_root=0))
        many = captured[0].labels(); captured.clear()
        ctl._multi = []
        ctl.cursor_time = 2.5
        ctl.show_selection_menu(Event(x_root=0, y_root=0), [ms[1]["id"]])
        one = captured[0].labels()
    finally:
        wt.tk.Menu = orig
    check("Merge 2 into One Card" in many and "Split Each in Half" in many and "Split Each into Words" in many
          and "Delete 2 Marks" in many, "selected marks' menu: merge / split / delete")
    check({"Split at @cursor", "Split in half", "Split into words (2)", "Merge with Previous", "Merge with Next"} <= set(one),
          "one card's menu: split at @cursor / in half / into words, merge with previous / next")
    h = ctl._mark_history_index
    ctl.merge_selection([ms[1]["id"], ms[2]["id"]])
    merged = ctl.mark_by_id(ms[1]["id"])
    check(merged["start"] == 2.0 and merged["end"] == 4.0 and merged["label"] == "w2 x2 w3 x3"
          and len(merged["pieces"]) == 2 and ctl._mark_history_index == h + 1,
          "Merge into One Card merges them (remembered for Unmerge), one undo step")
    n = ctl.split_selection("words", [ms[0]["id"], ms[3]["id"]])
    labels = sorted(m["label"] for m in ctl.track_marks(tr["id"]))
    check(n == 2 and "w1" in labels and "x1" in labels and "w4" in labels and ctl._mark_history_index == h + 2,
          "Split Each into Words splits every selected card in one undo step")
    ctl.undo_marks()
    check(len(ctl.track_marks(tr["id"])) == 3, "...and one undo puts them back")
    ctl.unmerge_selection([ms[1]["id"]])
    check(len(ctl.track_marks(tr["id"])) == 4, "Unmerge from the menu")


def test_round23(th, aa, wt, media):
    print("\n-- round 23: Beats 'Where', group highlight in the card editor, batch splits draw once --")
    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r23"), 20.0)
    rng = ctl._add_mark("range", 5.0, 9.0)
    ctl.cursor_time = 12.0
    ctl.selected = None
    check(ctl.analysis_range_why("auto")[:2] == (0.0, 20.0), "Where: nothing selected -> the whole song (default)")
    ctl.selected = ("mark", rng["id"])
    check(ctl.analysis_range_why("auto")[:2] == (5.0, 9.0), "...a selected range -> just that range")
    check(ctl.analysis_range_why("all")[:2] == (0.0, 20.0), "Where: the whole song, even with a selection")
    ctl.selected = None
    check(ctl.analysis_range_why("cursor")[:2] == (12.0, 20.0), "Where: from the @cursor to the end")
    wt.set_preference("beats_scope", "auto")
    check(ctl.beat_scope() == "auto", "the choice is remembered")
    real = aa.beats_available
    aa.beats_available = lambda: True
    try:
        ctl.beats_menu.entries.clear(); ctl._fill_beats_menu()
        labels = ctl.beats_menu.labels()
    finally:
        aa.beats_available = real
    check(any(l.startswith("Where: The selected range, else the whole song") for l in labels), "the Beats menu has Where \u25b8")

    # Shift+click: every card in the run is highlighted in the card editor
    ctl2, c2, _t2, _tab2 = bare_controller(wt, fresh_copy(media, "r23b"), 100.0)
    tr = ctl2._new_track("L")
    ms = [ctl2._add_mark("range", float(i), i + 0.9, label=f"w{i}", track_id=tr["id"]) for i in range(1, 7)]
    ctl2.selected = ("track", tr["id"]); ctl2.render_waveform(); run_afters()
    panel = ctl2.panel
    ctl2.select_mark(ms[0]["id"]); run_afters()
    ctl2.extend_selection(ms[4], toggle=False); run_afters()
    sel_bg = panel._card_bg(selected=True)
    painted = [panel.cards[m["id"]]["frame"].cget("bg") == sel_bg for m in ms]
    check(painted == [True, True, True, True, True, False], "Shift+click highlights every card of the run, not just the ends")

    # a batch draws once
    renders = []
    real_render = ctl2.render_waveform
    ctl2.render_waveform = lambda: (renders.append(1) if not getattr(ctl2, "_batch_depth", 0) else None,
                                    real_render())[1]
    ms2 = [m for m in ctl2.track_marks(tr["id"])]
    for m in ms2:
        m["label"] = "a b c"
    ctl2._multi = [m["id"] for m in ms2]
    ctl2.selected = ("mark", ms2[0]["id"])
    ctl2.split_selection("words")
    ctl2.render_waveform = real_render
    check(len(renders) == 1 and len(ctl2.track_marks(tr["id"])) == 18,
          "Split Each into Words redraws once at the end (not after every card)")


def test_round24(th, aa, wt, media):
    print("\n-- round 24: bar numbers on downbeats, text panel during long jobs, progress on one line --")
    beats = [0.5 * i for i in range(20)]
    b3 = th.beat_marks(beats, 0.0, 10.0, 4, 0, "beat", 3)
    check([m["label"] for m in b3[:3]] == ["1.3", "2.3", "3.3"], "Beat N is labeled bar.beat")
    late = th.beat_marks(beats, 3.0, 10.0, 4, 0, "beat", 1)
    check(late[0]["label"] == "1" and late[0]["start"] == 4.0, "bar numbers count from the first bar in the range")

    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r24"), 20.0)
    tr = ctl._new_track("Lyrics")
    m = ctl._add_mark("range", 1.0, 2.0, label="x", track_id=tr["id"])
    ctl.selected = ("mark", m["id"]); ctl.render_waveform(); run_afters()
    check(ctl.panel.mode == "track", "(a card is showing in the card editor)")
    ctl._set_analysis_busy("beats"); run_afters()
    check(ctl.selected is None and ctl.panel.mode == "info", "a long job switches to the text panel so its progress shows")
    ctl._set_analysis_busy(None); run_afters()
    check(ctl.selected == ("mark", m["id"]), "...and selects the card again when it's done")
    ctl._set_analysis_busy("beats")
    ctl.selected = ("track", tr["id"])                 # the job picks its own selection (e.g. the new track)
    ctl._set_analysis_busy(None)
    check(ctl.selected == ("track", tr["id"]), "...unless something else got selected meanwhile")
    ctl.selected = None; ctl.render_waveform(); run_afters()

    text = ctl.panel.text
    ctl.append_info("{blue}before\n")
    for pct in (10, 40, 90):
        ctl.progress_info(f"{{cyan}}  Beats: working ({pct}%)\n")
    ctl.append_info("{green}done\n")
    ctl.progress_info("{cyan}  next job (5%)\n")
    shown = text.get("1.0", "end")
    check(shown.count("Beats: working") == 1 and "(90%)" in shown and "(10%)" not in shown
          and shown.index("before") < shown.index("90%") < shown.index("done") < shown.index("next job"),
          "progress percentages update one line in place; other messages stay")
    check(ctl.info_text.count("Beats: working") == 1 and ctl.info_text.endswith("next job (5%)\n"),
          "...also in the saved info text (shown again after the card editor)")


def test_group_drag(th, aa, wt, media):
    print("\n-- dragging several selected marks together --")
    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r25"), 100.0)
    x_of = lambda t: int((t / 100.0) * 800)
    tr = ctl._new_track("Lyrics")
    other = ctl._new_track("Other")
    ms = [ctl._add_mark("range", float(s_), s_ + 8.0, label=f"m{s_}", track_id=tr["id"]) for s_ in (10, 20, 30, 40)]
    ctl.render_waveform()

    def band_y(track_id):
        for y in range(0, 600):
            z, t_ = ctl._track_zone_at_y(y)
            if z == "track" and t_ == track_id:
                return y + 3
    work_y = 30
    ctl.selected = ("mark", ms[1]["id"]); ctl._multi = [ms[1]["id"], ms[2]["id"], ms[3]["id"]]
    y = band_y(tr["id"])
    h = ctl._mark_history_index
    # drag the middle of one selected mark up onto the waveform
    ctl._on_waveform_press(Event(x=x_of(24.0), y=y))
    ctl._on_waveform_drag(Event(x=x_of(24.0), y=work_y))
    ctl._on_waveform_release(Event(x=x_of(24.0), y=work_y))
    moved = [ctl.mark_by_id(m["id"]) for m in ms[1:]]
    check(all(m.get("track_id") is None for m in moved) and ctl.mark_by_id(ms[0]["id"])["track_id"] == tr["id"],
          "dragging one of several selected marks onto the waveform takes all of them")
    check([m["start"] for m in moved] == [20.0, 30.0, 40.0], "...at their own times")
    check(ctl._mark_history_index == h + 1, "...one undo step")
    check(ctl.selected_mark_ids() == [m["id"] for m in moved], "...and they stay selected")
    # drag them along in time (same row): all move by the same amount
    ctl._on_waveform_press(Event(x=x_of(34.0), y=work_y + 10))
    ctl._on_waveform_drag(Event(x=x_of(39.0), y=work_y + 10, state=0x0001))
    ctl._on_waveform_release(Event(x=x_of(39.0), y=work_y + 10, state=0x0001))
    starts = [ctl.mark_by_id(m["id"])["start"] for m in ms[1:]]
    check(abs(starts[0] - 25.0) < 0.2 and abs((starts[1] - starts[0]) - 10.0) < 1e-6 and abs((starts[2] - starts[1]) - 10.0) < 1e-6,
          "dragging sideways moves the whole selection by the same time")
    # can't push the block past the end
    ctl._on_waveform_press(Event(x=x_of(44.0), y=work_y + 10))
    ctl._on_waveform_drag(Event(x=x_of(99.0), y=work_y + 10, state=0x0001))
    ctl._on_waveform_release(Event(x=x_of(99.0), y=work_y + 10, state=0x0001))
    last = ctl.mark_by_id(ms[3]["id"])
    check(last["end"] <= ctl.max_mark_time() + 1e-6 and
          abs((last["start"] - ctl.mark_by_id(ms[1]["id"])["start"]) - 20.0) < 1e-6,
          "...the block stops at the end without changing its spacing")
    # into another track
    ctl._on_waveform_press(Event(x=x_of(ctl.mark_by_id(ms[1]["id"])["start"] + 4.0), y=work_y + 10))
    oy = band_y(other["id"])
    ctl._on_waveform_drag(Event(x=x_of(ctl.mark_by_id(ms[1]["id"])["start"] + 4.0), y=oy))
    ctl._on_waveform_release(Event(x=x_of(ctl.mark_by_id(ms[1]["id"])["start"] + 4.0), y=oy))
    check(all(ctl.mark_by_id(m["id"])["track_id"] == other["id"] for m in ms[1:]), "...or into another track")
    # an edge still resizes just that mark; a plain click selects just one
    ctl._on_waveform_press(Event(x=x_of(ctl.mark_by_id(ms[2]["id"])["start"] + 4.0), y=band_y(other["id"])))
    ctl._on_waveform_release(Event(x=x_of(ctl.mark_by_id(ms[2]["id"])["start"] + 4.0), y=band_y(other["id"])))
    check(ctl.selected_mark_ids() == [ms[2]["id"]], "a click without dragging on one of them selects just that one")
    ctl.selected = ("mark", ms[0]["id"]); ctl._multi = []
    ctl._on_waveform_press(Event(x=x_of(14.0), y=band_y(tr["id"])))
    ctl._on_waveform_drag(Event(x=x_of(18.0), y=band_y(tr["id"]), state=0x0001))
    ctl._on_waveform_release(Event(x=x_of(18.0), y=band_y(tr["id"]), state=0x0001))
    check(abs(ctl.mark_by_id(ms[0]["id"])["start"] - 14.0) < 0.2 and ctl.mark_by_id(ms[2]["id"])["track_id"] == other["id"],
          "a single selected mark still drags on its own")


# ---------------------------------------------------------------------------


def test_round25(th, aa, wt, media):
    print("\n-- round 25: Beats menu picks work (tooltip over the menu, deferred picks, visible results) --")
    # Tooltip: never shown while a menu is posted (grab) or after the pointer moved on;
    # a second Enter doesn't leave an uncancellable timer behind.
    class Stub:
        def __init__(self):
            self.grab, self.under, self.timers, self.n = None, None, {}, 0
        def bind(self, *a, **k): pass
        def after(self, ms, fn):
            self.n += 1; self.timers[self.n] = fn; return self.n
        def after_cancel(self, i): self.timers.pop(i, None)
        def grab_current(self): return self.grab
        def winfo_pointerxy(self): return (1, 1)
        def winfo_containing(self, x, y): return self.under
        def winfo_rootx(self): return 0
        def winfo_rooty(self): return 0
        def winfo_height(self): return 20
    w = Stub()
    tip = wt._Tooltip(w, "help")
    tip._schedule(); tip._schedule()
    check(len(w.timers) == 1, "two Enters in a row leave one pending tooltip, not two")
    tip._hide()
    check(not w.timers, "...and leaving cancels it")
    w.grab = w
    tip._schedule()
    check(not w.timers, "no tooltip is scheduled while the button's menu holds the grab")
    w.grab = None
    tip._schedule()
    w.grab = w
    list(w.timers.values())[0]()
    check(tip._tip is None, "a tooltip due while the menu is open doesn't cover the menu")
    w.grab, w.under = None, object()
    tip._schedule(); list(w.timers.values())[0]()
    check(tip._tip is None, "...nor once the pointer is over something else")
    w.under = w
    tip._schedule(); list(w.timers.values())[0]()
    check(tip._tip is not None, "it still shows when resting on the button")
    tip._hide()

    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r25"), 20.0)
    check(ctl.beats_menu.cget("disabledforeground") == wt.TB_DISABLED,
          "greyed-out toolbar menu entries are visibly gray on the dark menu")
    beats = [round(0.5 * i, 3) for i in range(40)]
    real_avail, real_detect = aa.beats_available, aa.detect_beats
    aa.beats_available = lambda: True
    result = {"tempo": 120.0, "beats": beats, "strength": [1.0] * 40,
              "bass": [3.0 if i % 4 == 1 else 0.2 for i in range(40)]}
    aa.detect_beats = lambda path, progress=None: result
    try:
        wt.set_preference("beats_scope", "auto")
        ctl.selected = None
        ctl.beats_menu.entries.clear(); ctl._fill_beats_menu()
        subs_before = dict(ctl._beats_subs)
        ctl.beats_menu.invoke_label("All beats")
        check(not ctl.tracks, "a Beats pick runs after the menu has closed (not inside the menu's grab)")
        run_afters()
        check([t["name"] for t in ctl.tracks] == ["Beats"], "Beats \u25be > All beats makes a track")
        check("Beats" in ctl.play_status_var.get() and "new track" in ctl.play_status_var.get(),
              "...and says so on the status bar")
        ctl.beats_menu.entries.clear(); ctl._fill_beats_menu()
        check(ctl._beats_subs == subs_before and all(len(ctl._beats_subs[k].entries) > 0 for k in ctl._beats_subs),
              "the cascades are refilled, not re-created, each time the menu opens")
        sub = ctl._beats_subs["beat_n"]
        sub.invoke_label("Beat 3"); run_afters()
        check(ctl.tracks[-1]["name"] == "Beat 3", "Beat N of each bar \u25b8 Beat 3 works")
        ctl.beats_menu.invoke_label("Bars (numbered)"); run_afters()
        check(ctl.tracks[-1]["name"] == "Bars", "Bars works")

        # a selected card with no beat 1 in it: the reason is shown, not hidden behind the card editor
        tr = ctl._new_track("Lyrics")
        card = ctl._add_mark("range", 1.0, 1.2, label="word", track_id=tr["id"])
        ctl.selected = ("mark", card["id"]); ctl.render_waveform(); run_afters()
        n_tracks = len(ctl.tracks)
        ctl.run_beats("bars"); run_afters()
        check(len(ctl.tracks) == n_tracks and ctl.panel.mode == "info" and "No track made" in ctl.info_text,
              "no track made: the text panel shows why (the card editor no longer hides it)")
        check("no track made" in ctl.play_status_var.get(), "...and the status bar points to it")

        # detection fails on the first run: the error stays visible
        ctl3, _c3, _t3, _tab3 = bare_controller(wt, fresh_copy(media, "r25b"), 20.0)
        tr3 = ctl3._new_track("Lyrics")
        card3 = ctl3._add_mark("range", 1.0, 5.0, label="x", track_id=tr3["id"])
        ctl3.selected = ("mark", card3["id"]); ctl3.render_waveform(); run_afters()

        def boom(path, progress=None):
            raise RuntimeError("no backend")
        aa.detect_beats = boom
        ctl3.run_beats("beats"); run_afters()
        check(ctl3.panel.mode == "info" and "Beat detection error" in ctl3.info_text and not ctl3._analysis_busy,
              "a failed detection leaves its error on screen (card not re-selected over it)")
        ctl3._analysis_busy = "stems"
        ctl3.run_beats("beats")
        check("wait" in ctl3.play_status_var.get(), "picking Beats while another job runs says why nothing happens")
        ctl3._analysis_busy = None
    finally:
        aa.beats_available, aa.detect_beats = real_avail, real_detect



XSQ_XML = """<?xml version="1.0" encoding="UTF-8"?>
<xsequence BaseChannel="0" FixedPointTiming="1">
  <head>
    <version>2025.13.1</version>
    <author>Me</author>
    <song>Jingle</song>
    <sequenceTiming>25 ms</sequenceTiming>
    <sequenceType>Media</sequenceType>
    <mediaFile>C:\\\\Shows\\\\xsq_song.wav</mediaFile>
    <sequenceDuration>90.500</sequenceDuration>
  </head>
  <DisplayElements>
    <Element type="model" name="Yard" visible="1"/>
    <Element type="model" name="Star" visible="0"/>
    <Element type="model" name="MegaTree" visible="1"/>
    <Element type="model" name="Ghost" visible="1"/>
    <Element type="timing" name="Lyrics" visible="1"/>
  </DisplayElements>
  <ElementEffects>
    <Element type="model" name="Yard">
      <EffectLayer>
        <Effect ref="0" name="On" startTime="0" endTime="1000"/>
        <Effect ref="0" name="Twinkle" startTime="1000" endTime="2000"/>
      </EffectLayer>
      <EffectLayer/>
    </Element>
    <Element type="model" name="Star"><EffectLayer/></Element>
    <Element type="model" name="MegaTree">
      <EffectLayer><Effect ref="1" name="On" startTime="0" endTime="500"/></EffectLayer>
      <SubModelEffectLayer name="Top"><Effect ref="1" name="Bars" startTime="0" endTime="500"/></SubModelEffectLayer>
      <Strand index="0">
        <Effect ref="1" name="On" startTime="0" endTime="500"/>
        <Node index="2"><Effect ref="1" name="Off" startTime="0" endTime="500"/></Node>
      </Strand>
    </Element>
    <Element type="timing" name="Lyrics">
      <EffectLayer><Effect label="Hello world" startTime="0" endTime="1000"></Effect></EffectLayer>
      <EffectLayer>
        <Effect label="Hello" startTime="0" endTime="500"></Effect>
        <Effect label="world" startTime="500" endTime="1000"></Effect>
      </EffectLayer>
    </Element>
  </ElementEffects>
</xsequence>
"""


def test_round26(th, aa, wt, media):
    print("\n-- round 26: undo view, paste, card length/lock, Beats options, Structure --")
    import timing_panel as tp
    import utils
    # 1. undo/redo bring back the zoom/scroll the change was made in
    ctl, c, _t, _tab = bare_controller(wt, fresh_copy(media, "r26"), 100.0)
    ctl.view_start, ctl.view_end = 40.0, 50.0
    m = ctl._add_mark("range", 42.0, 44.0)
    ctl.view_start, ctl.view_end = 0.0, 100.0           # zoomed out / scrolled away meanwhile
    ctl.undo_marks()
    check((ctl.view_start, ctl.view_end) == (40.0, 50.0), "undo returns to the zoom/scroll the change was made in")
    ctl.view_start, ctl.view_end = 70.0, 80.0
    ctl.redo_marks()
    check((ctl.view_start, ctl.view_end) == (40.0, 50.0), "...and so does redo")
    check(len(ctl._history_views) == len(ctl._mark_history), "one remembered view per undo step")

    # 2. paste replaces the selection
    class StubEntry:
        def __init__(self, text, sel=None):
            self.text, self.sel, self.cursor = text, sel, len(text)
        def clipboard_get(self): return "1:02.500"
        def cget(self, k): return "normal"
        def selection_present(self): return self.sel is not None
        def delete(self, a, b):
            if (a, b) == ("sel.first", "sel.last"):
                if self.sel is None:
                    raise utils.tk.TclError("no selection")
                i, j = self.sel
                self.text, self.cursor, self.sel = self.text[:i] + self.text[j:], i, None
        def insert(self, where, s):
            self.text = self.text[:self.cursor] + s + self.text[self.cursor:]
            self.cursor += len(s)
    e = StubEntry("0:58.000", sel=(0, 8)); e.cursor = 8
    check(utils.paste_replacing_selection(e) and e.text == "1:02.500", "Ctrl+V replaces a field's selected text")
    e2 = StubEntry("0:58"); e2.cursor = 4
    utils.paste_replacing_selection(e2)
    check(e2.text == "0:581:02.500", "...and inserts at the cursor when nothing is selected")
    binds = []
    class Root:
        def bind_class(self, cls, seq, fn): binds.append((cls, seq))
    utils.install_paste_replaces_selection(Root())
    check(sorted(binds) == [("Entry", "<<Paste>>"), ("TEntry", "<<Paste>>"), ("Text", "<<Paste>>")],
          "...in every Entry and Text (only Tk's own <<Paste>> binding is replaced)")

    # 3-5. card length, End = Start, too short, the length lock
    ctl2, _c2, _t2, _tab2 = bare_controller(wt, fresh_copy(media, "r26b"), 100.0)
    tr = ctl2._new_track("L")
    a = ctl2._add_mark("range", 10.0, 12.5, label="a", track_id=tr["id"])
    b = ctl2._add_mark("range", 20.0, 21.0, label="b", track_id=tr["id"])
    ctl2.selected = ("track", tr["id"]); ctl2.render_waveform(); run_afters()
    panel = ctl2.panel
    card = panel.cards[a["id"]]
    check(card["dur"].cget("text") == "2.500 s", "a card shows its length")
    card["end"].delete(0, "end"); card["end"].insert(0, "0:10.005")
    panel._commit_time(a["id"], "end")
    shown_hint = panel._hint is not None
    run_afters()
    a = ctl2.mark_by_id(a["id"])
    check(a["end"] == 12.5 and "at least 10 ms" in panel.last_hint and "End = Start" in panel.last_hint,
          "too short an End is refused, with a note saying the minimum and how to make a mark")
    check("at least 10 ms" in ctl2.play_status_var.get(), "...also on the status bar")
    check(shown_hint and panel._hint is None, "...the note pops up under the field, then goes away by itself")
    panel.hide_hint()
    card["end"].delete(0, "end"); card["end"].insert(0, "0:10.000")
    panel._commit_time(a["id"], "end"); run_afters()
    a = ctl2.mark_by_id(a["id"])
    check(a["type"] == "point" and a["end"] is None, "End = Start makes the card a mark (no length)")
    check(panel.cards[a["id"]]["dur"].cget("text") == "mark", "...and its length reads \u201cmark\u201d")
    ctl2.undo_marks(); run_afters()
    a = ctl2.mark_by_id(a["id"])
    check(a["end"] == 12.5, "(undo)")
    panel._set_entry(panel.cards[a["id"]]["end"], "0:12.500")
    panel.step_var.set("1.0")
    ctl2.set_mark_times(a["id"], 10.0, 10.5); run_afters()
    panel.last_hint = ""
    panel._nudge(a["id"], "end", -1)
    a = ctl2.mark_by_id(a["id"])
    check(abs(a["end"] - 10.01) < 1e-9, "End \u2212 stops at the shortest length")
    panel._nudge(a["id"], "end", -1)
    check("at least 10 ms" in panel.last_hint, "...and pressing it again says why")
    ctl2.set_mark_times(a["id"], 10.0, 12.5); run_afters()
    # lock
    panel.toggle_lock(a["id"])
    check(panel.is_locked(a["id"]), "the padlock locks the card's length")
    card = panel.cards[a["id"]]
    card["start"].delete(0, "end"); card["start"].insert(0, "0:15.000")
    panel._commit_time(a["id"], "start"); run_afters()
    a = ctl2.mark_by_id(a["id"])
    check((a["start"], a["end"]) == (15.0, 17.5), "locked: a new Start moves the whole card")
    card = panel.cards[a["id"]]
    card["end"].delete(0, "end"); card["end"].insert(0, "0:16.000")
    panel._commit_time(a["id"], "end"); run_afters()
    a = ctl2.mark_by_id(a["id"])
    check((a["start"], a["end"]) == (13.5, 16.0), "...a new End too (the length stays 2.5 s)")
    panel.step_var.set("0.5")
    panel._nudge(a["id"], "start", 1)
    a = ctl2.mark_by_id(a["id"])
    check((a["start"], a["end"]) == (14.0, 16.5), "...and \u2212/+ move it as a whole")
    panel._move_locked(a["id"], start=-5.0)
    a = ctl2.mark_by_id(a["id"])
    check((a["start"], a["end"]) == (0.0, 2.5), "...never before 0")
    h = ctl2._mark_history_index
    panel._move_locked(a["id"], start=4.0)
    check(ctl2._mark_history_index == h + 1, "...one undo step per move")
    panel.toggle_lock(a["id"])
    check(not panel.is_locked(a["id"]), "click again: unlocked")
    pt = ctl2._add_mark("point", 30.0, None, label="p", track_id=tr["id"]); ctl2.render_waveform(); run_afters()
    check(panel.cards[pt["id"]]["lock"].cget("state") == "disabled", "a mark with no length has no lock")

    # 6. Beats: length and labels
    beats = [0.5 * i for i in range(17)]
    specs = th.beat_marks(beats, 0.0, 8.0, 4, 0, "beat", 1)
    fill = th.style_beat_marks(specs, "fill", True, beats=beats, end=8.0)
    check([(m["start"], m["end"]) for m in fill] == [(0.0, 2.0), (2.0, 4.0), (4.0, 6.0), (6.0, 8.0)],
          "Length: up to the next mark -- downbeats touch, the last one a bar long")
    one = th.style_beat_marks(specs, "beat", True, beats=beats, end=8.0)
    check([m["end"] - m["start"] for m in one] == [0.5] * 4, "Length: one beat")
    lines = th.style_beat_marks(specs, "lines", False, beats=beats)
    check(all(m["end"] is None and m["label"] == "" for m in lines), "Length: no length (lines), labels off")
    real_avail, real_detect = aa.beats_available, aa.detect_beats
    aa.beats_available = lambda: True
    aa.detect_beats = lambda path, progress=None: {"tempo": 120.0, "beats": beats, "strength": [1.0] * 17,
                                                   "bass": [3.0 if i % 4 == 0 else 0.1 for i in range(17)]}
    try:
        wt.set_preference("beats_scope", "all")
        wt.set_preference("beats_length", "lines"); wt.set_preference("beats_labels", False)
        ctl2.selected = None
        ctl2.run_beats("beat", 1); run_afters()
        bm = ctl2.track_marks(ctl2.tracks[-1]["id"])
        check(bm and all(m["type"] == "point" and m["label"] == "" for m in bm),
              "Beats \u25be with Length: lines and labels off makes unlabeled point marks")
        ctl2.beats_menu.entries.clear(); ctl2._fill_beats_menu()
        labels = ctl2.beats_menu.labels()
        check(any(l.startswith("Length: No length") for l in labels)
              and any(l.startswith("Label the marks") for l in labels), "the menu has Length \u25b8 and Label the marks")
    finally:
        aa.beats_available, aa.detect_beats = real_avail, real_detect
        wt.set_preference("beats_length", "fill"); wt.set_preference("beats_labels", True)

    # 7. Structure
    import numpy as np
    rng = np.random.default_rng(2)
    pattern = "IABABCBBO"
    proto = {L: rng.normal(size=25) for L in sorted(set(pattern))}
    feats = [list(proto[L] + rng.normal(scale=0.7, size=25)) for L in pattern for _ in range(16)]
    found = aa.find_sections(feats, list(range(0, len(feats), 4)), min_beats=16)
    check(found["bounds"] == [0, 16, 32, 48, 64, 80, 96, 128, 144], "Structure: section boundaries at the changes")
    check("".join(found["letters"]) == "ABCBCDCE", "...repeats get the same letter (B B in a row is one section)")
    names = aa.name_sections(found["letters"], [0.2, 0.5, 0.9, 0.5, 0.9, 0.6, 0.9, 0.3])
    check(names == ["Intro", "Verse 1", "Chorus 1", "Verse 2", "Chorus 2", "Bridge", "Chorus 3", "Outro"],
          "...names: loudest repeat = Chorus, other repeat = Verse, one-offs = Intro/Bridge/Outro")
    check(aa.name_sections(list("ABCBCA"), [0.2, 0.5, 0.9, 0.5, 0.9, 0.2])[0] == "Intro"
          and aa.name_sections(list("ABCBCA"), [0.2, 0.5, 0.9, 0.5, 0.9, 0.2])[-1] == "Outro",
          "...a part heard only at the start and the end is Intro / Outro")
    check(aa.name_sections(list("ABCD"), [1, 1, 1, 1], vocal=[None, 0.0, 0.8, None])[1] == "Instrumental",
          "...a one-off part without vocals (stems known) is Instrumental")
    ctl3, _c3, _t3, _tab3 = bare_controller(wt, fresh_copy(media, "r26c"), 80.0)
    times = [0.5 * i for i in range(len(feats))]
    calls = {"n": 0}

    def fake_struct(path, progress=None):
        calls["n"] += 1
        return {"tempo": 120.0, "beats": times, "strength": [1.0] * len(times),
                "bass": [3.0 if i % 4 == 0 else 0.1 for i in range(len(times))],
                "features": feats, "rms": [{"I": .2, "A": .5, "B": .9, "C": .6, "O": .3}[pattern[i // 16]]
                                           for i in range(len(times))]}
    real_s, real_sa = aa.structure_features, aa.structure_available
    aa.structure_features, aa.structure_available = fake_struct, (lambda: True)
    try:
        wt.set_preference("structure_names", "guess"); wt.set_preference("structure_min_bars", 4)
        ctl3.structure_menu.entries.clear(); ctl3._fill_structure_menu()
        ctl3.structure_menu.invoke_label("Find sections \u2192 new \u201cStructure\u201d track"); run_afters()
        tr3 = ctl3.tracks[-1]
        sm = sorted(ctl3.track_marks(tr3["id"]), key=lambda m: m["start"])
        check(tr3["name"] == "Structure" and [m["label"] for m in sm][:3] == ["Intro", "Verse 1", "Chorus 1"],
              "Structure \u25be > Find sections makes a \u201cStructure\u201d track of named sections")
        check(sm[0]["start"] == 0.0 and sm[-1]["end"] == 80.0 and all(m["source"] == "structure" for m in sm)
              and all(abs(x["end"] - y["start"]) < 1e-9 for x, y in zip(sm, sm[1:])),
              "...covering the whole song, touching")
        check(getattr(ctl3, "_beat_cache", None) is not None, "...and Beats \u25be reuses its beats (no second analysis)")
        wt.set_preference("structure_names", "both")
        ctl3.run_structure(); run_afters()
        sm2 = sorted(ctl3.track_marks(ctl3.tracks[-1]["id"]), key=lambda m: m["start"])
        check(calls["n"] == 1 and sm2[1]["label"] == "Verse 1 \u00b7 B" and ctl3.tracks[-1]["name"] == "Structure 2",
              "...run again: analyzed once per file; Names: Both adds the letter")
        labels = ctl3.structure_menu.labels()
        check(any(l.startswith("Shortest section: 4 bars") for l in labels) and any(l.startswith("Names:") for l in labels),
              "the Structure menu has Names \u25b8 and Shortest section \u25b8")
    finally:
        aa.structure_features, aa.structure_available = real_s, real_sa
        wt.set_preference("structure_names", "guess")


def test_xsq_tab():
    print("\n-- xsq_tab: an xLights sequence --")
    import xsq_tab as xq
    import utils
    show = os.path.join(tempfile.mkdtemp(prefix="tracked_xsq_"), "xsqshow")     # nothing above it
    seqdir = os.path.join(show, "Sequences", "2025")
    os.makedirs(seqdir, exist_ok=True)
    path = os.path.join(seqdir, "song.xsq")
    with open(path, "w") as f:
        f.write(XSQ_XML)
    with open(os.path.join(seqdir, "xsq_song.wav"), "wb") as f:
        f.write(b"RIFF")
    other = os.path.join(TMP, "notseq.xsq")
    with open(other, "w") as f:
        f.write("<?xml version='1.0'?><something/>")
    check(xq.is_xsq_file(path) and not xq.is_xsq_file(other), "only an .xsq with an <xsequence> root is taken")
    seq = xq.parse_xsq(path)
    info = seq["info"]
    check(info["version"] == "2025.13.1" and info["duration"] == 90.5 and info["frame_ms"] == 25
          and info["fps"] == 40.0, "head: version, duration, 25 ms frames = 40 fps")
    mt = seq["elements"]["MegaTree"]
    check(mt["own"] == 1 and mt["parts"] == {"Top": 1, "Strand 1": 1, "Strand 1 / Node 3": 1} and mt["effects"] == 4,
          "effects counted on the model, its submodels, strands and nodes")
    check(seq["order"] == ["Yard", "Star", "MegaTree", "Ghost"] and seq["elements"]["Star"]["visible"] is False,
          "elements in the sequence's order, with Visible")
    check(seq["timing"]["Lyrics"]["layers"] == [1, 2] and seq["total"] == 6,
          "timing tracks: marks per layer (not counted as effects)")
    check(xq.find_media(info["media"], path) == os.path.join(seqdir, "xsq_song.wav"),
          "the media file (a Windows path) is found by name next to the sequence")
    utils.set_preference(xq.PREF_SHOW_FOLDER, None)
    check(xq.find_show_folder(path) is None, "no layout anywhere above: no show folder")
    with open(os.path.join(show, "xlights_rgbeffects.xml"), "w") as f:
        f.write(LAYOUT_XML)
    check(xq.find_show_folder(path) == show, "the show folder is found two levels up")

    canvas, text, tab = FakeCanvas(FakeWidget()), FakeText(), FakeTab()
    check(xq.onload(path, canvas=canvas, text=text, tab=tab), "the plugin claims the sequence")
    view = canvas._xsq_view
    summary = text.get()
    check("2025.13.1" in summary and "40 fps" in summary and "Lyrics: " in summary
          and "1 group, 2 models, 1 not in the layout" in summary
          and "found here as" in summary and tab.protect_file, "summary in the text panel; the file is protected")
    rows = {r["element"]: r for r in view.shown}
    check(rows["Yard"]["kind"] == "group" and rows["Star"]["kind"] == "model" and rows["Ghost"]["kind"] == "not in layout",
          "Kind from the show folder's layout: group / model / not in layout")
    tree = view.tree
    check([tree.item(i)["text"] for i in tree.get_children()] == ["Yard", "Star", "MegaTree", "Ghost"],
          "the list starts in the sequence's order")
    check(len(tree.get_children("e:MegaTree")) == 3, "...submodels / strands / nodes as child rows")
    view.sort_by("effects")
    check([tree.item(i)["text"] for i in tree.get_children()][:2] == ["MegaTree", "Yard"],
          "clicking Effects sorts most first")
    view.only_fx.set(True); view._toggle_only_fx()
    check(len(tree.get_children()) == 2, "Only with effects hides the empty ones")
    view.only_fx.set(False); view._toggle_only_fx()
    view.set_filter("types", "Twinkle")
    check([tree.item(i)["text"] for i in tree.get_children()] == ["Yard"], "filter by effect type")
    view.set_filter("effects", ">=2")
    check(len(tree.get_children()) == 2, "...or by a count")
    view.clear_filter(); view.file_order()
    check(tree.item(tree.get_children()[0])["text"] == "Yard", "File order puts it back")
    check(xq.types_text(xq.Counter({"On": 3, "Bars": 1, "Off": 1, "Twinkle": 1}), 2) == "On 3, Bars 1, +2 more",
          "effect types: most used first")



def test_round27(th, aa, wt, media):
    print("\n-- round 27: option clicks keep the Beats / Structure / Stems menus open --")
    ctl, _c, _t, _tab = bare_controller(wt, fresh_copy(media, "r27"), 30.0)
    popped = []
    for name in ("beats_menu", "structure_menu", "stems_menu"):
        menu = getattr(ctl, name)
        menu.tk_popup = lambda x, y, n=name: popped.append(n)
    real_avail = aa.beats_available
    aa.beats_available = lambda: True
    try:
        wt.set_preference("beats_labels", True); wt.set_preference("beats_length", "fill")
        ctl.beats_menu.entries.clear(); ctl._fill_beats_menu()
        ctl.beats_menu.invoke_label("Label the marks (beat / bar numbers)")
        check(not popped, "(the menu comes back once Tk has closed it, not inside the click)")
        run_afters()
        check(popped == ["beats_menu"], "turning Label the marks on/off keeps the Beats menu open")
        ctl._beats_subs["length"].invoke_label("No length (lines)"); run_afters()
        check(popped[-1] == "beats_menu" and wt.get_preference("beats_length") == "lines",
              "picking a Length opens the Beats menu again (its label shows the new choice)")
        ctl.beats_menu.entries.clear(); ctl._fill_beats_menu()
        check(any(e.get("label") == "Length: No length (lines)" for e in ctl.beats_menu.entries),
              "...Length: No length (lines)")
        for key, label in (("per_bar", "3"), ("where", wt.WaveformController.BEAT_SCOPES[1][1])):
            n = len(popped)
            ctl._beats_subs[key].invoke_label(label); run_afters()
            check(len(popped) == n + 1, f"...also Beats per bar / Where ({key})")
        ran = []
        ctl.run_metronome = lambda *a, **k: ran.append("metronome")
        ctl.beats_menu.entries.clear(); ctl._fill_beats_menu()
        n = len(popped)
        ctl.beats_menu.invoke_label("Metronome..."); run_afters()
        check(ran == ["metronome"] and len(popped) == n, "an action (Metronome..., All beats...) still closes the menu")
        ctl.structure_menu.entries.clear(); ctl._fill_structure_menu()
        ctl._structure_subs["bars"].invoke_label("8 bars"); run_afters()
        check(popped[-1] == "structure_menu" and wt.get_preference("structure_min_bars") == 8,
              "Structure: Shortest section keeps its menu open")
        ctl._structure_subs["names"].invoke_label(wt.WaveformController.STRUCTURE_NAMES[1][1]); run_afters()
        check(popped[-1] == "structure_menu", "...and Names")
        ctl._set_regions([{"start": 0.0, "end": 5.0, "kind": "vocal"}, {"start": 5.0, "end": 9.0, "kind": "novocal"}])
        ctl.stems_menu.entries.clear(); ctl._fill_stems_menu()
        ctl.stems_menu.invoke_label("   Merge touching regions of different stems"); run_afters()
        check(popped[-1] == "stems_menu", "Stems \u25be: Merge touching regions keeps the menu open")
    finally:
        aa.beats_available = real_avail
        wt.set_preference("beats_length", "fill"); wt.set_preference("beats_per_bar", 4)
        wt.set_preference("beats_scope", "auto"); wt.set_preference("structure_min_bars", 4)
        wt.set_preference("structure_names", "guess")



def test_xsq_loops():
    print("\n-- xsq_tab: loops, repeated passages, copied rows --")
    import xsq_tab as xq

    def eff(st, en, name="On", ref="1", pal="0"):
        return f'<Effect ref="{ref}" name="{name}" startTime="{st}" endTime="{en}" palette="{pal}"/>'
    # A and B: a 2 s pattern repeated 4 times from 4 s (back to back) -> one loop 4..12 s
    # C: one-off effects; D: copy of A (same effects); E: 1 s passage at 1 s, again at 20 s
    pat = lambda base: "".join(eff(base + o, base + o + 400, n, r)
                               for o, n, r in ((0, "On", "1"), (500, "Twinkle", "2"), (1000, "Bars", "3")))
    a = "".join(pat(4000 + 2000 * k) for k in range(4))
    b = "".join(eff(4000 + 2000 * k + 1500, 4000 + 2000 * k + 1900, "Off", "4") for k in range(4))
    passage = lambda base: "".join(eff(base + o, base + o + 300, "Fan", "5") for o in (0, 300, 600, 900))
    xml = f"""<?xml version="1.0" encoding="UTF-8"?>
<xsequence><head><version>2025.1</version><sequenceTiming>50 ms</sequenceTiming>
<mediaFile>x.wav</mediaFile><sequenceDuration>30.000</sequenceDuration></head>
<DisplayElements><Element type="model" name="A"/><Element type="model" name="B"/><Element type="model" name="C"/>
<Element type="model" name="D"/><Element type="model" name="E"/><Element type="model" name="Base"/></DisplayElements>
<ElementEffects>
<Element type="model" name="A"><EffectLayer>{a}</EffectLayer></Element>
<Element type="model" name="B"><EffectLayer>{b}</EffectLayer><SubModelEffectLayer name="Top">{a}</SubModelEffectLayer></Element>
<Element type="model" name="C"><EffectLayer>{eff(1000, 1500, "Text", "9")}{eff(14000, 15000, "Text", "9")}</EffectLayer></Element>
<Element type="model" name="D"><EffectLayer/><EffectLayer>{a}</EffectLayer></Element>
<Element type="model" name="E"><EffectLayer>{passage(16000)}{eff(18000, 18500, "Text", "8")}{passage(24000)}</EffectLayer></Element>
<Element type="model" name="Base"><EffectLayer>{eff(0, 30000, "Color Wash", "7")}</EffectLayer></Element>
</ElementEffects></xsequence>"""
    path = os.path.join(tempfile.mkdtemp(prefix="tracked_xsql_"), "loops.xsq")
    with open(path, "w") as f:
        f.write(xml)
    seq = xq.parse_xsq(path)
    check(len(seq["rows"][("A", "")]) == 12 and len(seq["rows"][("B", "Top")]) == 12,
          "each row's effects are kept (element, submodel) for comparing")
    copies = xq.find_copied_rows(seq)
    check(copies == [[("A", ""), ("B", "Top"), ("D", "")]],
          "copied rows: A, B's submodel Top and D (another layer) have exactly the same effects")
    found = xq.find_loops(seq, duration_ms=30000)
    loops = found["loops"]
    check(len(loops) == 1 and (loops[0]["start"], loops[0]["end"], loops[0]["period"]) == (4000, 12000, 2000)
          and loops[0]["repeats"] == 4.0, "a loop: 0:04-0:12, every 2 s, 4 times")
    check(("A", "") in loops[0]["rows"] and ("B", "") in loops[0]["rows"],
          "...across all the rows that repeat (the whole-song Color Wash doesn't break it)")
    ps = found["passages"]
    check(len(ps) == 1 and (ps[0]["start"], ps[0]["end"], ps[0]["period"]) == (16000, 17200, 8000),
          "a repeated passage: 0:16-0:17.2 again at 0:24 (something else in between)")
    report = xq.loops_report(seq, found, copies)
    check("Loop 1: {cyan}0:04.000\u20130:12.000" in report and "every 2.000 s (4\u00d7)" in report
          and "again at {cyan}0:24.000" in report and "A, B / Top, D" in report, "the report lists them")
    # a single strand of changes: no loop
    check(xq.find_loops({"rows": {("X", ""): [(0, i * 1000, i * 1000 + 500, ("On", str(i), "0")) for i in range(20)]}},
                        duration_ms=30000) == {"loops": [], "passages": []}, "all-different effects: no loops")
    # overlapping finds: the longest wins, then the shorter period
    rows = {("X", ""): [(0, i * 1000, i * 1000 + 500, ("On", "1", "0")) for i in range(20)]}
    lp = xq.find_loops({"rows": rows}, duration_ms=20000)["loops"]
    check(len(lp) == 1 and lp[0]["period"] == 1000 and (lp[0]["start"], lp[0]["end"]) == (0, 20000),
          "overlapping loops (every 1 s / 2 s / ...): the largest, with the shortest period")

    # the view: Same as column, Find loops in the background
    canvas, text, tab = FakeCanvas(FakeWidget()), FakeText(), FakeTab()
    xq.onload(path, canvas=canvas, text=text, tab=tab)
    view = canvas._xsq_view
    tree = view.tree
    check(tree.item("e:A")["values"][-1] == "= B / Top, D" and tree.item("e:D")["values"][-1] == "= A, B / Top",
          "Same as column names the copies")
    check(tree.item("p:B/Top")["values"][-1] == "= A, D", "...also on a submodel's row")
    check("Copied rows: " in text.get() and "1 set of rows" in text.get(), "the summary mentions copied rows")
    view.set_filter("same", "A")
    check([tree.item(i)["text"] for i in tree.get_children()] == ["D"], "filter on Same as")
    view.clear_filter()
    check(view.find_loops(), "Find loops starts")
    view._loop_thread.join(10)
    run_afters()
    check(view._loop_thread is None and "Loop 1:" in text.get() and "[xsq_tab] {green}" not in text.get()
          and "1 loop, 1 repeated passage, 1 copied set" == view.status_var.get(),
          "...the report appears under the summary; the status line counts them")
    before = text.get()
    view.find_loops()
    check(view._loop_thread is None and text.get() == before, "...a second click shows it again (no new search)")



def test_xsq_loop_settings():
    print("\n-- xsq_tab: nudge tolerance, rows left out of loop checking --")
    import xsq_tab as xq
    import xlayout_tab as xlt
    import utils
    sig = lambda n: ("On", str(n), "0")
    # a 1 s pattern of 4 effects, repeated 10 times; repeats 3 and 7 nudged by 1 frame (50 ms)
    def row(nudged=(3,), shift=50):
        out = []
        for k in range(10):
            dk = shift if k in nudged else 0
            for o, n in ((0, 1), (200, 2), (400, 3), (600, 4)):
                out.append((0, k * 1000 + o + dk, k * 1000 + o + 150 + dk, sig(n)))
        return out
    seq = {"rows": {("M", ""): row(), ("N", ""): row(())}, "order": ["M", "N"], "info": {"frame_ms": 50}}
    exact = xq.find_loops(seq, duration_ms=20000, tol_ms=0)["loops"]
    loose = xq.find_loops(seq, duration_ms=20000, tol_ms=50)["loops"]
    check(not any(l["end"] - l["start"] >= 9000 for l in exact), "exact matching: nudged repeats break the loop")
    check(len(loose) == 1 and (loose[0]["start"], loose[0]["period"]) == (0, 1000) and loose[0]["end"] >= 10000,
          "1 frame of tolerance: one 1 s loop across the nudges")
    check(xq.find_copied_rows(seq, 0) == [] and xq.find_copied_rows(seq, 50) == [[("M", ""), ("N", "")]],
          "copied rows: a nudged copy matches within the tolerance only")
    check(xq.find_copied_rows(seq, 49) == [], "...not when the nudge is bigger than the tolerance")
    check(xq._pick_shifts(xq.Counter({1000: 30, 1050: 3, 950: 3, 2000: 20}), 50, 4)[:2] == [1000, 2000],
          "nearby repeat distances (nudges) are pooled; one distance per pool is tried")
    # exclusions
    check(xq.parse_patterns("Arch*\n# comment\n  Tree / Top  \nArch*\n\n") == ["Arch*", "Tree / Top"],
          "the exclusion list: one per line, # comments, duplicates dropped")
    seq2 = {"rows": {("Arch 1", ""): [], ("Arch 2", "Seg"): [], ("Tree", "Top"): [], ("Tree", ""): [],
                     ("Star [1]", ""): []}, "order": []}
    check(xq.excluded_rows(seq2, ["arch*"]) == {("Arch 1", ""), ("Arch 2", "Seg")},
          "a wildcard (any case) leaves out models and all their submodels")
    check(xq.excluded_rows(seq2, ["Tree / Top"]) == {("Tree", "Top")}, "\u201cModel / Submodel\u201d leaves out one part")
    check(xq.excluded_rows(seq2, [xq.glob_escape("Star [1]")]) == {("Star [1]", "")},
          "a name with [ ] * ? is matched literally when added by right-click")
    # controller assignment from the layout
    mc = xlt.model_controller
    check(mc({"Controller": "Falcon F16"}) == "Falcon F16" and mc({"StartChannel": "!PixLite:1"}) == "PixLite"
          and mc({"Controller": "No Controller", "StartChannel": "1"}) is not None
          and mc({"Controller": "No Controller"}) is None and mc({}) is None,
          "controller: the Controller attribute, a !Controller:n start channel, or an absolute channel")
    layout = {"models": {"A": {"controller": "F16"}, "B": {"controller": None}, "C": {"controller": None}},
              "groups": {"G1": {"models": ["B", "C"], "groups": []}, "G2": {"models": ["A", "B"], "groups": []},
                         "G3": {"models": [], "groups": ["G1"]}}}
    check(xq.no_controller_names(layout) == {"B", "C", "G1", "G3"},
          "no controller: those models, and groups made only of them (nested too)")

    # the view
    path = os.path.join(tempfile.mkdtemp(prefix="tracked_xsqs_"), "set.xsq")
    def effs(base_nudge=0):
        return "".join(f'<Effect ref="{n}" name="On" startTime="{k*1000+o+(base_nudge if k == 4 else 0)}" '
                       f'endTime="{k*1000+o+150+(base_nudge if k == 4 else 0)}" palette="0"/>'
                       for k in range(8) for o, n in ((0, 1), (300, 2), (600, 3), (800, 4)))
    with open(path, "w") as f:
        f.write(f"""<?xml version="1.0"?><xsequence><head><sequenceTiming>50 ms</sequenceTiming>
<sequenceDuration>10.000</sequenceDuration></head><DisplayElements>
<Element type="model" name="Loop"/><Element type="model" name="Copy"/><Element type="model" name="Noise"/>
</DisplayElements><ElementEffects>
<Element type="model" name="Loop"><EffectLayer>{effs()}</EffectLayer></Element>
<Element type="model" name="Copy"><EffectLayer>{effs(50)}</EffectLayer></Element>
<Element type="model" name="Noise"><EffectLayer><Effect ref="9" name="Text" startTime="2500" endTime="2600" palette="0"/>
</EffectLayer></Element></ElementEffects></xsequence>""")
    utils.set_preference(xq.PREF_TOLERANCE, 1)
    utils.set_preference(xq.PREF_EXCLUDE, [])
    utils.set_preference(xq.PREF_SKIP_NO_CONTROLLER, False)
    canvas, text, tab = FakeCanvas(FakeWidget()), FakeText(), FakeTab()
    xq.onload(path, canvas=canvas, text=text, tab=tab)
    view = canvas._xsq_view
    check(view.tree.item("e:Loop")["values"][-1] == "= Copy", "Same as uses the tolerance (Copy is nudged 1 frame)")
    view.find_loops(); view._loop_thread.join(10); run_afters()
    check("Loop 2: 0:02.600" in text.get() and "within 50 ms (1 frame)" in text.get(),
          "the Noise effect splits the loop in two; the report says how close times must be")
    view.set_excluded([("Noise", "")], True); view._loop_thread and view._loop_thread.join(10); run_afters()
    check(view.patterns() == ["Noise"] and "excluded" in view.tree.item("e:Noise")["tags"],
          "right-click > Leave out: added to the list, the row is crossed out")
    check("Loop 1: 0:00.000\u20130:08.000" in text.get() and "Loop 2:" not in text.get()
          and "Not checked for loops (1 row): Noise" in text.get(),
          "...the report is worked out again at once: one loop, and it says what wasn't checked")
    view.set_excluded([("Noise", "")], False); view._loop_thread and view._loop_thread.join(10); run_afters()
    check(view.patterns() == [] and "Loop 2:" in text.get(), "Check for loops again undoes it")
    view.apply_settings(tolerance_frames=0); view._loop_thread and view._loop_thread.join(10); run_afters()
    check(view.tree.item("e:Loop")["values"][-1] == "" and "exactly equal" in text.get(),
          "tolerance 0: the nudged copy no longer counts")
    view.loop_settings_dialog()
    st = view._settings
    check(st["tolerance"].get() == "0" and not st["no_controller"].get(), "Loop settings... shows the current settings")
    st["tolerance"].set("2"); st["box"].insert("end", "No*\n# old stuff\n")
    st["ok"](); view._loop_thread and view._loop_thread.join(10); run_afters()
    check(view.tolerance_frames() == 2 and view.patterns() == ["No*"] and "Loop 1:" in text.get()
          and "Loop 2:" not in text.get(),
          "...OK saves them (and the report follows)")
    utils.set_preference(xq.PREF_TOLERANCE, xq.DEFAULT_TOLERANCE_FRAMES)
    utils.set_preference(xq.PREF_EXCLUDE, [])


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
    test_xsq_tab()
    test_xsq_loops()
    test_xsq_loop_settings()

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
        test_fast_destroy()
        test_input_methods()
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
        test_round14(th, aa, wt, media)
        test_round15(th, aa, wt, media)
        test_round16(th, aa, wt, media)
        test_round17(th, aa, wt, media)
        test_round18(th, aa, wt, media)
        test_round19(th, aa, wt, media)
        test_round20(th, aa, wt, media)
        test_round21(th, aa, wt, media)
        test_round22(th, aa, wt, media)
        test_round23(th, aa, wt, media)
        test_round24(th, aa, wt, media)
        test_round25(th, aa, wt, media)
        test_group_drag(th, aa, wt, media)
        test_round26(th, aa, wt, media)
        test_round27(th, aa, wt, media)

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
