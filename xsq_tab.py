"""
xsq_tab.py -- trackED plugin for an xLights sequence (.xsq).

Read-only view of a sequence: what it plays, how long, at what frame rate,
and which models and groups have effects -- the file is never written.

  text panel  a summary: xLights version, media file (and whether it's found
              here), duration, timing (ms per frame and fps), file size,
              author/song/artist when set; element counts (groups, models,
              timing tracks), the effect types used most, and each timing
              track with its marks per layer (e.g. phrases / words /
              phonemes).
  list        one row per model / group, in the sequence's own order:
              Element, Kind (group / model / "not in layout"), Effects (all,
              including submodels and strands), Own (on the element's own
              layers), Sub/strand (on its submodels, strands and nodes),
              Layers, Visible, Effect types. Elements with effects on
              submodels or strands open to show them as child rows.
              Click a heading to sort (again: reverse); the filter box takes
              the same syntax as the layout tab ("=On", "!Twinkle", ">10",
              "1-5"). "Only with effects" hides the empty ones.

              Same as: the other rows (models, groups, submodels, strands)
              with exactly the same effects -- copy+pasted rows.
  Find loops  (toolbar, runs in the background) adds a report under the
              summary: loops (a stretch whose effects repeat back to back
              every N seconds on the same rows; overlapping finds -> the
              longest), repeated passages (a stretch that comes again later,
              not back to back), and the sets of copied rows. "The same"
              means same effect type, settings and palette, with start and
              end within the nudge tolerance; effects running the whole song
              are ignored for loops.
  Loop settings...  tolerance in frames (default 1), "leave out models with
              no controller" (needs the show folder), and a list of names
              (wildcards * ?; "Model / Submodel" for one part) left out of
              loop checking. Right-click rows to add / remove them. Left-out
              rows are crossed out; copied rows still include them.

Groups vs. models: the .xsq only names its elements; which ones are groups
comes from the show folder's xlights_rgbeffects.xml. It is looked for in
the sequence's folder and the folders above it; "Show folder..." picks it
by hand (remembered). Without it the Kind column says "?".

The pure logic (parse_xsq, element_rows, filter/sort, the summary) needs no
Tk and is unit-tested in tests.py.
"""

from __future__ import annotations

import bisect
import fnmatch
import re
import threading
import time
import xml.etree.ElementTree as ET
from collections import Counter
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import tkinter as tk
from tkinter import ttk, filedialog

from utils import debug, get_preference, insert_styled_text, set_preference

import xlayout_tab as xl

XSQ_EXTS = {".xsq"}
FILE_TYPES = [("xLights sequence", "*.xsq")]       # File > Open (tracked.py)
LAYOUT_NAME = "xlights_rgbeffects.xml"
PREF_SHOW_FOLDER = "xsq_show_folder"
PREF_TOLERANCE = "xsq_tolerance_frames"         # Loop settings: nudge tolerance in frames
PREF_EXCLUDE = "xsq_loop_exclude"                # Loop settings: names / patterns left out of loops
PREF_SKIP_NO_CONTROLLER = "xsq_skip_no_controller"
DEFAULT_TOLERANCE_FRAMES = 1
MAX_TOLERANCE_FRAMES = 10
EXCLUDED_FG = "#a8a8a8"
PARENT_LEVELS = 6                                   # how far up to look for the show folder
COLUMNS = ("element", "kind", "effects", "own", "parts", "layers", "visible", "types", "same")
HEADINGS = {"element": "Element", "kind": "Kind", "effects": "Effects", "own": "Own",
            "parts": "Sub/strand", "layers": "Layers", "visible": "Visible", "types": "Effect types",
            "same": "Same as"}
NUMERIC = ("effects", "own", "parts", "layers")
ANY_COLUMN = "Any column"
NOT_IN_LAYOUT = "not in layout"
UNKNOWN_KIND = "?"
TOP_TYPES = 3                                       # effect types shown per row

FG, FG_DIM, BG, FIELD_BG = xl.FG, xl.FG_DIM, xl.BG, xl.FIELD_BG
SEL_BG, SEL_FG = xl.SEL_BG, xl.SEL_FG
ROW_BG, ROW_ALT_BG = xl.ROW_BG, xl.ROW_ALT_BG
EMPTY_FG = "#9a9a9a"                                # rows without effects


# ===========================================================================
# Pure logic (no Tk)
# ===========================================================================

def is_xsq_file(path: str) -> bool:
    """A .xsq file whose root element is <xsequence>."""
    p = Path(path)
    if p.suffix.lower() not in XSQ_EXTS or not p.is_file():
        return False
    try:
        with open(p, "rb") as f:
            head = f.read(4096)
    except OSError:
        return False
    return re.search(rb"<xsequence[\s>/]", head) is not None


def _float(text: Optional[str]) -> Optional[float]:
    try:
        return float((text or "").strip())
    except ValueError:
        return None


def frame_ms(timing: str) -> Optional[int]:
    """"50 ms" -> 50 (xLights' <sequenceTiming>)."""
    m = re.match(r"\s*(\d+(?:\.\d+)?)\s*(?:ms)?\s*$", timing or "")
    return int(round(float(m.group(1)))) if m else None


def _effects_in(el, sink: Optional[List[Tuple]] = None, layer: int = 0) -> Tuple[int, Counter]:
    """Effects directly inside one layer element, and their types. With
    sink: also appends (layer, start ms, end ms, signature) per effect; the
    signature (name, settings ref, palette) is equal for identical effects
    (xLights stores each distinct settings string / palette once)."""
    types: Counter = Counter()
    n = 0
    for eff in el.findall("Effect"):
        n += 1
        name = eff.get("name") or "(unnamed)"
        types[name] += 1
        if sink is not None:
            sink.append((layer, _int(eff.get("startTime")), _int(eff.get("endTime")),
                         (name, eff.get("ref", ""), eff.get("palette", ""))))
    return n, types


def parse_xsq(path: str) -> Dict[str, Any]:
    """Read an xLights sequence:
    {"info": {version, media, duration, frame_ms, fps, type, author, song,
              artist, album, comment},
     "elements": {name: {"name", "type" ("model"), "visible", "own",
                  "layers", "parts": {part name: effects}, "effects",
                  "types": Counter}},   (models/groups, in display order)
     "order": [...],
     "timing": {name: {"layers": [marks per layer], "labeled": [...],
                "marks": total}},
     "types": Counter (all effects), "total": all effects}.
    Submodel layers (<SubModelEffectLayer name=...>) count under their
    name; strands (<Strand index=i>) as "Strand i+1" and their nodes as
    "Strand i+1 / Node j+1"."""
    root = ET.parse(path).getroot()
    if root.tag != "xsequence":
        raise ValueError(f"not an xLights sequence (root <{root.tag}>)")
    head = root.find("head")
    h = {c.tag: (c.text or "").strip() for c in head} if head is not None else {}
    ms = frame_ms(h.get("sequenceTiming", ""))
    info = {"version": h.get("version", ""), "media": h.get("mediaFile", ""),
            "duration": _float(h.get("sequenceDuration")), "frame_ms": ms,
            "fps": (1000.0 / ms) if ms else None, "type": h.get("sequenceType", ""),
            "author": h.get("author", ""), "song": h.get("song", ""), "artist": h.get("artist", ""),
            "album": h.get("album", ""), "comment": h.get("comment", "")}

    elements: Dict[str, Dict[str, Any]] = {}
    timing: Dict[str, Dict[str, Any]] = {}
    order: List[str] = []
    display = root.find("DisplayElements")
    visible: Dict[str, bool] = {}
    for el in (display.findall("Element") if display is not None else []):
        name = el.get("name") or ""
        visible[name] = el.get("visible", "1") != "0"
        if el.get("type") == "timing":
            timing.setdefault(name, {"layers": [], "labeled": [], "marks": 0})
        elif name not in elements:
            elements[name] = _new_element(name, visible[name])
            order.append(name)

    total_types: Counter = Counter()
    rows: Dict[Tuple[str, str], List[Tuple]] = {}      # (element, part) -> effects (see _effects_in)
    effects_el = root.find("ElementEffects")
    for el in (effects_el.findall("Element") if effects_el is not None else []):
        name = el.get("name") or ""
        if el.get("type") == "timing":
            t = timing.setdefault(name, {"layers": [], "labeled": [], "marks": 0})
            for layer in el.findall("EffectLayer"):
                marks = layer.findall("Effect")
                t["layers"].append(len(marks))
                t["labeled"].append(sum(1 for m in marks if (m.get("label") or "").strip()))
            t["marks"] = sum(t["layers"])
            continue
        e = elements.get(name)
        if e is None:
            e = elements[name] = _new_element(name, visible.get(name, True))
            order.append(name)
        layer_no: Counter = Counter()           # layer index within each row

        def sink(part):
            return rows.setdefault((name, part), [])
        for child in el:
            if child.tag == "EffectLayer":
                n, types = _effects_in(child, sink(""), layer_no[""])
                layer_no[""] += 1
                e["layers"] += 1
                e["own"] += n
                e["types"].update(types)
            elif child.tag == "SubModelEffectLayer":
                part = child.get("name") or "(submodel)"
                n, types = _effects_in(child, sink(part), layer_no[part])
                layer_no[part] += 1
                e["parts"][part] = e["parts"].get(part, 0) + n
                e["types"].update(types)
            elif child.tag == "Strand":
                idx = _int(child.get("index"))
                n, types = _effects_in(child, sink(f"Strand {idx + 1}"))
                e["parts"][f"Strand {idx + 1}"] = e["parts"].get(f"Strand {idx + 1}", 0) + n
                e["types"].update(types)
                for node in child.findall("Node"):
                    key = f"Strand {idx + 1} / Node {_int(node.get('index')) + 1}"
                    m, ntypes = _effects_in(node, sink(key))
                    e["parts"][key] = e["parts"].get(key, 0) + m
                    e["types"].update(ntypes)
        e["effects"] = e["own"] + sum(e["parts"].values())
        total_types.update(e["types"])
    rows = {k: v for k, v in rows.items() if v}
    return {"info": info, "elements": elements, "order": order, "timing": timing,
            "types": total_types, "total": sum(total_types.values()), "rows": rows}


def _int(text: Optional[str]) -> int:
    try:
        return int(float(text or 0))
    except ValueError:
        return 0


def _new_element(name: str, visible: bool) -> Dict[str, Any]:
    return {"name": name, "type": "model", "visible": visible, "own": 0, "layers": 0,
            "parts": {}, "effects": 0, "types": Counter()}


def find_show_folder(xsq_path: str, preferred: Optional[str] = None) -> Optional[str]:
    """The folder holding xlights_rgbeffects.xml: the one picked by hand
    (if it still has the file), else the sequence's folder or one above."""
    if preferred and (Path(preferred) / LAYOUT_NAME).is_file():
        return str(Path(preferred))
    here = Path(xsq_path).resolve().parent
    for folder in [here] + list(here.parents)[:PARENT_LEVELS]:
        if (folder / LAYOUT_NAME).is_file():
            return str(folder)
    return None


def find_media(media: str, xsq_path: str, show_folder: Optional[str] = None) -> Optional[str]:
    """The sequence's media file here: as written (often a path on the
    machine that made it), else a file of that name next to the sequence
    or in the show folder."""
    if not media:
        return None
    if Path(media).is_file():
        return media
    name = re.split(r"[\\/]", media)[-1]
    for folder in [Path(xsq_path).resolve().parent] + ([Path(show_folder)] if show_folder else []):
        cand = folder / name
        if cand.is_file():
            return str(cand)
    return None


# ---------------------------------------------------------------------------
# Copied rows and loops
# ---------------------------------------------------------------------------

def row_label(key: Tuple[str, str]) -> str:
    """("MegaTree", "Top") -> "MegaTree / Top"; the element's own row: its name."""
    return key[0] if not key[1] else f"{key[0]} / {key[1]}"


def _row_lanes(effects) -> Dict[Tuple, List[Tuple[int, int]]]:
    """signature -> sorted (start, end) of one row's effects (any layer)."""
    lanes: Dict[Tuple, List[Tuple[int, int]]] = {}
    for _layer, st, en, sig in effects:
        lanes.setdefault(sig, []).append((st, en))
    for v in lanes.values():
        v.sort()
    return lanes


def _rows_match(a: Dict[Tuple, List], b: Dict[Tuple, List], tol: int) -> bool:
    if a.keys() != b.keys():
        return False
    for sig, xs in a.items():
        ys = b[sig]
        if len(xs) != len(ys):
            return False
        for (s1, e1), (s2, e2) in zip(xs, ys):
            if abs(s1 - s2) > tol or abs(e1 - e2) > tol:
                return False
    return True


def find_copied_rows(seq: Dict[str, Any], tol_ms: int = 0) -> List[List[Tuple[str, str]]]:
    """Rows (model / group, or one of its submodels, strands, nodes) that
    have the same effects as another row -- same type, settings and
    palette, and start/end times within tol_ms (nudges): groups of 2+ row
    keys, the rows with the most effects first, each group in the
    sequence's order. Which layer an effect sits on is ignored."""
    order = {name: i for i, name in enumerate(seq.get("order", []))}
    lanes = {key: _row_lanes(effects) for key, effects in seq.get("rows", {}).items()}
    buckets: Dict[Tuple, List[Tuple[str, str]]] = {}
    for key, ln in lanes.items():          # only rows with the same effect kinds/counts can match
        shape = tuple(sorted((sig, len(v)) for sig, v in ln.items()))
        if tol_ms <= 0:
            shape = (shape, tuple(sorted((sig, tuple(v)) for sig, v in ln.items())))
        buckets.setdefault(shape, []).append(key)
    parent: Dict[Tuple[str, str], Tuple[str, str]] = {}

    def find(x):
        while parent.get(x, x) != x:
            parent[x] = parent.get(parent[x], parent[x])
            x = parent[x]
        return x
    for keys in buckets.values():
        if len(keys) < 2:
            continue
        if tol_ms <= 0:
            for k in keys[1:]:
                parent[find(k)] = find(keys[0])
            continue
        for i, k1 in enumerate(keys):
            for k2 in keys[i + 1:]:
                if find(k1) != find(k2) and _rows_match(lanes[k1], lanes[k2], tol_ms):
                    parent[find(k2)] = find(k1)
    groups_by_root: Dict[Tuple[str, str], List[Tuple[str, str]]] = {}
    for key in lanes:
        groups_by_root.setdefault(find(key), []).append(key)
    groups = [sorted(g, key=lambda k: (order.get(k[0], 1 << 30), k[1]))
              for g in groups_by_root.values() if len(g) > 1]
    groups.sort(key=lambda g: (-len(seq["rows"][g[0]]), order.get(g[0][0], 1 << 30)))
    return groups


def same_as_map(groups: List[List[Tuple[str, str]]]) -> Dict[Tuple[str, str], List[Tuple[str, str]]]:
    """row key -> the other rows with the same effects."""
    out: Dict[Tuple[str, str], List[Tuple[str, str]]] = {}
    for g in groups:
        for k in g:
            out[k] = [o for o in g if o != k]
    return out


# ---------------------------------------------------------------------------
# Rows left out of loop checking
# ---------------------------------------------------------------------------

def glob_escape(name: str) -> str:
    """A model name as a pattern that matches only itself."""
    return re.sub(r"([*?\[])", r"[\1]", name)


def parse_patterns(text: str) -> List[str]:
    """One name per line; * and ? are wildcards; # starts a comment."""
    out = []
    for line in (text or "").splitlines():
        line = line.split("#", 1)[0].strip()
        if line and line not in out:
            out.append(line)
    return out


def _matches_pattern(label: str, pattern: str) -> bool:
    return fnmatch.fnmatchcase(label.casefold(), pattern.casefold())


def no_controller_names(layout: Optional[Dict[str, Any]]) -> set:
    """Models with no controller, and groups whose models all have none."""
    if not layout:
        return set()
    out = {name for name, m in layout["models"].items() if not m.get("controller")}
    for name, g in layout["groups"].items():
        members = group_models(layout, name)
        if members and all(m in out for m in members):
            out.add(name)
    return out


def group_models(layout: Dict[str, Any], name: str, _seen=None) -> List[str]:
    """All models in a group, through nested groups."""
    seen = _seen if _seen is not None else set()
    if name in seen:
        return []
    seen.add(name)
    g = layout["groups"].get(name)
    if g is None:
        return []
    out = [m for m in g["models"] if m in layout["models"]]
    for child in g["groups"]:
        out += [m for m in group_models(layout, child, seen) if m not in out]
    return out


def excluded_rows(seq: Dict[str, Any], patterns: List[str], skip_no_controller: bool = False,
                  layout: Optional[Dict[str, Any]] = None) -> set:
    """Row keys left out of loop checking: an element matching a pattern
    (with all its submodels/strands), a "Element / Part" pattern for one
    part, and -- if asked and the layout is known -- models with no
    controller (and groups made only of them)."""
    nocon = no_controller_names(layout) if skip_no_controller else set()
    out = set()
    for key in seq.get("rows", {}):
        name = key[0]
        if name in nocon or any(_matches_pattern(name, p) or _matches_pattern(row_label(key), p)
                                for p in patterns):
            out.add(key)
    return out


MIN_LOOP_EFFECTS = 4          # a loop has at least this many effects repeated
MAX_SHIFTS = 16               # repeat distances tried (the most common ones)
MAX_PASSAGES = 10             # repeated passages reported (longest first)
PAIR_REACH = 12               # each effect is paired with this many later twins at most


def _loop_events(seq: Dict[str, Any], duration_ms: Optional[int], exclude=None):
    """Effects that can take part in a loop: not empty, not on an excluded
    row, and not running the whole song (a base layer from start to end
    never repeats, but doesn't break a loop either)."""
    whole = None if not duration_ms else duration_ms - 50
    exclude = exclude or set()
    return [(key, layer, st, en, sig) for key, effects in seq.get("rows", {}).items() if key not in exclude
            for layer, st, en, sig in effects
            if en > st and not (whole is not None and st <= 50 and en >= whole)]


class _Twins:
    """Looks up "the same effect, shifted by d" -- exactly, or with start
    and end each within tol ms."""

    def __init__(self, events, tol: int):
        self.tol = tol
        self.exact = {(k, l, st, en, sig) for k, l, st, en, sig in events}
        self.lanes: Dict[Tuple, Tuple[List[int], List[int]]] = {}
        if tol > 0:
            tmp: Dict[Tuple, List[Tuple[int, int]]] = {}
            for k, l, st, en, sig in events:
                tmp.setdefault((k, l, sig), []).append((st, en))
            for lane, spans in tmp.items():
                spans.sort()
                self.lanes[lane] = ([a for a, _b in spans], [b for _a, b in spans])

    def has(self, k, l, sig, st, en) -> bool:
        if (k, l, st, en, sig) in self.exact:
            return True
        if self.tol <= 0:
            return False
        lane = self.lanes.get((k, l, sig))
        if lane is None:
            return False
        starts, ends = lane
        i = bisect.bisect_left(starts, st - self.tol)
        while i < len(starts) and starts[i] <= st + self.tol:
            if abs(ends[i] - en) <= self.tol:
                return True
            i += 1
        return False


def find_loops(seq: Dict[str, Any], min_effects: int = MIN_LOOP_EFFECTS,
               duration_ms: Optional[int] = None, tol_ms: int = 0,
               exclude=None) -> Dict[str, List[Dict[str, Any]]]:
    """Repeats in the timeline, on the same rows and layers, with the same
    effects (type, settings, palette; start and end within tol_ms):

    "loops":    stretches that repeat back to back: from `start`, every
                `period` ms the same effects come again, up to `end`
                (`repeats` periods). Overlapping finds: the longest is kept
                (on a tie, the shorter period).
    "passages": a stretch [start, end) that comes again `period` later, with
                something different in between (not back to back). Ones a
                kept loop already explains are left out.
    Rows in `exclude` (row keys) and effects running the whole song are
    ignored. Times in ms. Each entry also has "effects" (repeated effects
    in the first copy) and "rows"."""
    events = _loop_events(seq, duration_ms, exclude)
    out: Dict[str, List[Dict[str, Any]]] = {"loops": [], "passages": []}
    if len(events) < 2 * min_effects:
        return out
    tol = max(0, int(tol_ms))
    twins = _Twins(events, tol)
    lanes: Dict[Tuple, List[Tuple[int, int]]] = {}
    for k, l, st, en, sig in events:
        lanes.setdefault((k, l, sig), []).append((st, en))
    votes: Counter = Counter()
    for spans in lanes.values():
        spans.sort()
        for i, (a0, a1) in enumerate(spans):
            for b0, b1 in spans[i + 1:i + 1 + PAIR_REACH]:
                d = b0 - a0
                if d > 2 * tol and abs((b1 - a1) - d) <= 2 * tol:
                    votes[d] += 1
    shifts = _pick_shifts(votes, tol, min_effects)
    loops, passages = [], []
    for d in shifts:
        for found in _repeats_at(events, twins, d, min_effects, duration_ms):
            (loops if found["loop"] else passages).append(found)
    loops.sort(key=lambda lp: (-(lp["end"] - lp["start"]), lp["period"], lp["start"]))
    kept: List[Dict[str, Any]] = []
    for lp in loops:
        if all(lp["end"] <= k["start"] or lp["start"] >= k["end"] for k in kept):
            kept.append(lp)

    def inside_loop(a, b, period):
        return any(k["start"] <= a + tol and b <= k["end"] + tol + 1 and _divides(k["period"], period, tol)
                   for k in kept)

    def in_a_loop(a, b):
        return any(a < k["end"] and b > k["start"] for k in kept)

    def explained(p):
        # both copies in loops of a matching period, or both overlapping a loop
        # (a partial match inside a loop's own pattern is a coincidence, not news)
        a, b, d = p["start"], p["end"], p["period"]
        return ((inside_loop(a, b, d) and inside_loop(a + d, b + d, d))
                or (in_a_loop(a, b) and in_a_loop(a + d, b + d)))
    passages.sort(key=lambda p: (-(p["end"] - p["start"]), p["period"], p["start"]))
    kept_p: List[Dict[str, Any]] = []
    for p in passages:
        if explained(p):
            continue
        if all(p["end"] <= q["start"] or p["start"] >= q["end"] for q in kept_p):
            kept_p.append(p)
    for x in kept + kept_p:
        del x["loop"]
    out["loops"] = sorted(kept, key=lambda x: x["start"])
    out["passages"] = sorted(kept_p[:MAX_PASSAGES], key=lambda x: x["start"])     # the longest ones
    return out


def _divides(small: int, big: int, tol: int) -> bool:
    if small <= 0:
        return False
    n = max(1, round(big / small))
    return abs(big - n * small) <= max(tol, 0) * n


def _pick_shifts(votes: Counter, tol: int, min_effects: int) -> List[int]:
    """The most-voted repeat distances. With a tolerance, nudged copies
    spread their votes over nearby distances: those within tol are pooled,
    and only the best distance of each pool is tried."""
    if tol <= 0:
        return [d for d, n in votes.most_common(MAX_SHIFTS) if n >= min_effects]
    ds = sorted(votes)
    pooled = {}
    j0 = j1 = 0
    total = 0
    for d in ds:                                   # sliding window [d - tol, d + tol]
        while j1 < len(ds) and ds[j1] <= d + tol:
            total += votes[ds[j1]]
            j1 += 1
        while ds[j0] < d - tol:
            total -= votes[ds[j0]]
            j0 += 1
        pooled[d] = (total, votes[d])
    chosen: List[int] = []
    for d in sorted(pooled, key=lambda x: (-pooled[x][0], -pooled[x][1], x)):
        if pooled[d][0] < min_effects or len(chosen) >= MAX_SHIFTS:
            break
        if all(abs(d - c) > tol for c in chosen):
            chosen.append(d)
    return chosen


def _repeats_at(events, twins, d, min_effects, duration_ms):
    """Runs of the timeline (in "source" time) where every effect starting
    there has its twin d later, and every effect starting d later has its
    twin there. A run checked for at least one whole period repeats back to
    back (a loop); a shorter one is a repeated passage."""
    checks: Dict[int, bool] = {}
    info: Dict[int, List[Tuple]] = {}
    for k, l, st, en, sig in events:
        fwd = twins.has(k, l, sig, st + d, en + d)
        checks[st] = checks.get(st, True) and fwd
        if fwd:
            info.setdefault(st, []).append((k, en))
        t = st - d                                    # this effect as the copy of one d earlier
        if t >= -twins.tol:
            t = max(0, t)
            checks[t] = checks.get(t, True) and twins.has(k, l, sig, st - d, en - d)
    results = []
    times = sorted(checks)
    limit = duration_ms if duration_ms else max(en for _k, _l, _s, en, _g in events)
    i = 0
    while i < len(times):
        if not checks[times[i]]:
            i += 1
            continue
        j = i
        while j + 1 < len(times) and checks[times[j + 1]]:
            j += 1
        run = times[i:j + 1]
        # checked up to the next failing start (else to where the copy would leave the song)
        stop = times[j + 1] if j + 1 < len(times) else limit - d
        matched = [x for t in run for x in info.get(t, [])]
        if len(matched) >= min_effects:
            start = run[0]
            src_end = max(en for _k, en in matched)
            if stop - start >= d - twins.tol:          # a whole period checked: back-to-back repeats
                end = min(limit, max(src_end, stop) + d) if j + 1 < len(times) else min(limit, src_end + d)
                results.append({"loop": True, "start": start, "end": end, "period": d,
                                "repeats": round((end - start) / d, 2), "effects": len(matched),
                                "rows": sorted({k for k, _en in matched})})
            else:
                results.append({"loop": False, "start": start, "end": min(src_end, stop), "period": d,
                                "repeats": 2, "effects": len(matched),
                                "rows": sorted({k for k, _en in matched})})
        i = j + 1
    return results


def ms_text(ms: int) -> str:
    m, s = divmod(ms / 1000.0, 60.0)
    return f"{int(m)}:{s:06.3f}"


def loops_report(seq: Dict[str, Any], found: Dict[str, List[Dict[str, Any]]],
                 copies: List[List[Tuple[str, str]]], max_names: int = 6,
                 excluded: Optional[set] = None, tol_ms: int = 0) -> str:
    """Styled text for the text panel after "Find loops"."""
    def names_text(keys):
        names = [row_label(k) for k in keys]
        more = f", +{len(names) - max_names} more" if len(names) > max_names else ""
        return f"{len(names)} row{'' if len(names) == 1 else 's'}: {{cyan}}{', '.join(names[:max_names])}{more}"
    out = ["\n{cyan}[xsq_tab] {green}Loops, repeated passages and copied rows\n"]
    fms = seq["info"].get("frame_ms") or 0
    frames = f" ({round(tol_ms / fms):g} frame{'' if round(tol_ms / fms) == 1 else 's'})" if fms and tol_ms else ""
    out.append(f"{{blue}}  Matching: same effect, settings and palette; times "
               + (f"within {tol_ms} ms{frames}" if tol_ms else "exactly equal") + ".\n")
    if excluded:
        names = sorted({row_label(k) for k in excluded})
        more = f", +{len(names) - max_names} more" if len(names) > max_names else ""
        out.append(f"{{blue}}  Not checked for loops ({len(names)} row{'' if len(names) == 1 else 's'}): "
                   f"{{cyan}}{', '.join(names[:max_names])}{more}\n")
    loops, passages = found.get("loops", []), found.get("passages", [])
    if not loops:
        out.append(f"{{yellow}}  No loops found (a loop repeats at least {MIN_LOOP_EFFECTS} effects back to back).\n")
    for i, lp in enumerate(loops, 1):
        out.append(f"{{blue}}  Loop {i}: {{cyan}}{ms_text(lp['start'])}\u2013{ms_text(lp['end'])}  "
                   f"{{blue}}every {lp['period'] / 1000:.3f} s ({lp['repeats']:g}\u00d7), "
                   f"{lp['effects']} effects on " + names_text(lp["rows"]) + "\n")
    for i, p in enumerate(passages, 1):
        out.append(f"{{blue}}  Repeated passage {i}: {{cyan}}{ms_text(p['start'])}\u2013{ms_text(p['end'])}  "
                   f"{{blue}}again at {{cyan}}{ms_text(p['start'] + p['period'])}\u2013"
                   f"{ms_text(p['end'] + p['period'])}{{blue}}, {p['effects']} effects on "
                   + names_text(p["rows"]) + "\n")
    if not copies:
        out.append("{yellow}  No copied rows (no two rows have the same effects).\n")
    else:
        out.append(f"{{blue}}  Copied rows ({len(copies)} set{'' if len(copies) == 1 else 's'} "
                   "with the same effects):\n")
        for g in copies:
            n = len(seq["rows"][g[0]])
            names = [row_label(k) for k in g]
            more = f", +{len(names) - max_names} more" if len(names) > max_names else ""
            out.append(f"{{cyan}}    {', '.join(names[:max_names])}{more}  "
                       f"{{blue}}({n} effect{'' if n == 1 else 's'} each)\n")
    return "".join(out)


def element_kind(name: str, layout: Optional[Dict[str, Any]]) -> str:
    if layout is None:
        return UNKNOWN_KIND
    if name in layout["groups"]:
        return "group"
    if name in layout["models"]:
        return "model"
    return NOT_IN_LAYOUT


def types_text(types: Counter, limit: int = TOP_TYPES) -> str:
    """"On 3, Twinkle 1, +2 more" (most used first)."""
    common = sorted(types.items(), key=lambda kv: (-kv[1], kv[0]))
    text = ", ".join(f"{name} {n}" for name, n in common[:limit])
    if len(common) > limit:
        text += f", +{len(common) - limit} more"
    return text


def same_as_text(key: Tuple[str, str], same: Dict[Tuple[str, str], List[Tuple[str, str]]],
                 limit: int = 2) -> str:
    """"= Star, MegaTree / Top, +3 more" -- the other rows with exactly
    this row's effects ("" when none)."""
    others = same.get(key) or []
    if not others:
        return ""
    text = ", ".join(row_label(k) for k in others[:limit])
    if len(others) > limit:
        text += f", +{len(others) - limit} more"
    return "= " + text


def copies_of(seq: Dict[str, Any]) -> List[List[Tuple[str, str]]]:
    """find_copied_rows(seq) at the sequence's current tolerance
    (seq["_tol_ms"], set by the view), worked out once per tolerance."""
    tol = int(seq.get("_tol_ms", 0) or 0)
    cache = seq.setdefault("_copies", {})
    if tol not in cache:
        cache[tol] = find_copied_rows(seq, tol)
    return cache[tol]


def element_rows(seq: Dict[str, Any], layout: Optional[Dict[str, Any]]) -> List[Dict[str, Any]]:
    same = same_as_map(copies_of(seq))
    rows = []
    for i, name in enumerate(seq["order"]):
        e = seq["elements"][name]
        rows.append({"element": name, "kind": element_kind(name, layout), "effects": e["effects"],
                     "own": e["own"], "parts": sum(e["parts"].values()), "layers": e["layers"],
                     "visible": e["visible"], "types": types_text(e["types"]),
                     "same": same_as_text((name, ""), same), "order": i})
    return rows


def visible_text(value: bool) -> str:
    return "\u2713" if value else ""


def _shown(row: Dict[str, Any], col: str):
    return visible_text(row[col]) if col == "visible" else row[col]


def filter_rows(rows: List[Dict[str, Any]], column: str, spec: str,
                only_with_effects: bool = False) -> List[Dict[str, Any]]:
    if only_with_effects:
        rows = [r for r in rows if r["effects"]]
    if not (spec or "").strip():
        return list(rows)
    if column in COLUMNS:
        return [r for r in rows if xl.matches(r[column], spec, numeric=(column in NUMERIC))]
    if spec.strip().startswith("!"):
        return [r for r in rows if all(xl.matches(_shown(r, c), spec) for c in COLUMNS)]
    return [r for r in rows if any(xl.matches(_shown(r, c), spec) for c in COLUMNS)]


def sort_rows(rows: List[Dict[str, Any]], column: Optional[str], reverse: bool = False,
              case_sensitive: bool = True) -> List[Dict[str, Any]]:
    """None: the sequence's own order. Otherwise by the column (then by
    name); empty values last either way; Visible: shown ones first."""
    if column is None:
        return sorted(rows, key=lambda r: r["order"], reverse=reverse)
    rows = sorted(rows, key=lambda r: xl.natural_key(r["element"], case_sensitive))
    if column == "visible":
        return sorted(rows, key=lambda r: 0 if r["visible"] else 1, reverse=reverse)
    filled = [r for r in rows if r[column] not in (None, "")]
    empty = [r for r in rows if r[column] in (None, "")]
    return sorted(filled, key=lambda r: xl.natural_key(r[column], case_sensitive), reverse=reverse) + empty


def _size_text(n: int) -> str:
    for unit in ("bytes", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:,} bytes" if unit == "bytes" else f"{n:.1f} {unit}"
        n /= 1024.0
    return str(n)


def _duration_text(seconds: Optional[float]) -> str:
    if seconds is None:
        return "?"
    m, s = divmod(seconds, 60.0)
    return f"{int(m)}:{s:06.3f}  ({seconds:.3f} s)"


def xsq_summary(path: str, seq: Dict[str, Any], show_folder: Optional[str],
                layout: Optional[Dict[str, Any]], media_found: Optional[str]) -> str:
    """Styled text for the text panel."""
    info = seq["info"]
    out = [f"{{cyan}}[xsq_tab] {{green}}{Path(path).name}\n"]

    def line(label, value, color="cyan"):
        out.append(f"{{blue}}  {label}: {{{color}}}{value}\n")
    line("xLights version", info["version"] or "?")
    line("Sequence type", info["type"] or "?")
    media = info["media"] or "(none)"
    if info["media"]:
        if media_found and media_found != info["media"]:
            media += f"\n      found here as {media_found}"
        elif not media_found:
            media += "  (not found on this computer)"
    line("Media", media, "cyan" if (media_found or not info["media"]) else "yellow")
    line("Duration", _duration_text(info["duration"]))
    if info["frame_ms"]:
        line("Timing", f"{info['frame_ms']} ms per frame ({info['fps']:.3g} fps)")
    try:
        line("File size", _size_text(Path(path).stat().st_size))
    except OSError:
        pass
    for key, label in (("song", "Song"), ("artist", "Artist"), ("album", "Album"), ("author", "Author"),
                       ("comment", "Comment")):
        if info.get(key):
            line(label, info[key])

    rows = element_rows(seq, layout)
    kinds = Counter(r["kind"] for r in rows)
    with_fx = sum(1 for r in rows if r["effects"])
    out.append("\n")
    if layout is None:
        out.append("{yellow}  Show folder not found (no xlights_rgbeffects.xml here or above): groups and "
                   "models can't be told apart. Use \u201cShow folder...\u201d above the list.\n")
    else:
        out.append(f"{{blue}}  Show folder: {{cyan}}{show_folder}\n")
    parts = [f"{len(rows)} models/groups"]
    if layout is not None:
        ng, nm = kinds.get("group", 0), kinds.get("model", 0)
        parts = [f"{ng} group{'' if ng == 1 else 's'}", f"{nm} model{'' if nm == 1 else 's'}"]
        if kinds.get(NOT_IN_LAYOUT):
            parts.append(f"{kinds[NOT_IN_LAYOUT]} not in the layout")
    line("Elements", ", ".join(parts) + f"; {len(seq['timing'])} timing tracks")
    line("With effects", f"{with_fx} of {len(rows)} ({seq['total']} effects)")
    if seq["types"]:
        line("Effect types", types_text(seq["types"], limit=8))
    copies = copies_of(seq)
    if copies:
        n = sum(len(g) for g in copies)
        line("Copied rows", f"{len(copies)} set{'' if len(copies) == 1 else 's'} of rows with the same "
                            f"effects ({n} rows; see Same as, or Find loops for the list)")
    if seq["timing"]:
        out.append("{blue}  Timing tracks:\n")
        for name, t in seq["timing"].items():
            layers = " / ".join(str(n) for n in t["layers"]) or "0"
            what = "layer" if len(t["layers"]) == 1 else "layers"
            marks = f"{t['marks']} mark{'' if t['marks'] == 1 else 's'}"
            out.append(f"{{cyan}}    {name}: {{blue}}{marks} ({what}: {layers})\n")
    return "".join(out)


# ===========================================================================
# Plugin entry
# ===========================================================================

def onload(filepath: str, canvas=None, text=None, tab=None):
    if not is_xsq_file(filepath):
        return False
    if canvas is None:
        return True                     # probe only
    path = str(Path(filepath).resolve())
    try:
        seq = parse_xsq(path)
    except Exception as exc:            # a broken file: say so instead of failing silently
        debug(1, f"{{red}}xsq: {path}: {exc}")
        if text is not None:
            text.delete("1.0", "end")
            insert_styled_text(text, f"{{cyan}}[xsq_tab]\n{{red}}Couldn't read {Path(path).name}: {exc}\n")
        if tab is not None:
            tab.protect_file = True
        return True
    view = XsqView(canvas, path, seq, tab=tab, text=text)
    canvas._xsq_view = view             # keep it alive
    if tab is not None:
        tab.protect_file = True         # the text panel is a summary: never saved over the sequence
        tab.min_sash = view.min_panel_height
        tab.preferred_sash = view.preferred_panel_height
        tab.title_detail = f"{len(seq['elements'])} models/groups, {seq['total']} effects"
    view.show_summary()
    debug(1, f"{{green}}xsq: {path}: {len(seq['elements'])} elements, {seq['total']} effects")
    return True


# ===========================================================================
# The view (Tk)
# ===========================================================================

class XsqView:
    """Toolbar (filter, only-with-effects, show folder) over one list."""

    def __init__(self, canvas, path: str, seq: Dict[str, Any], tab=None, text=None):
        self.canvas = canvas
        self.path = path
        self.seq = seq
        self.tab = tab
        self.text = text
        self.sort_column: Optional[str] = None       # None: the sequence's order
        self.sort_reverse = False
        self.shown: List[Dict[str, Any]] = []
        self._loops = None
        self._report_shown = False
        self._apply_tolerance()
        self.load_layout()
        self._build()
        self.refresh()

    # ------------------------------------------------------------------ show folder / layout
    def load_layout(self):
        self.show_folder = find_show_folder(self.path, get_preference(PREF_SHOW_FOLDER, None))
        self.layout = None
        if self.show_folder:
            try:
                self.layout = xl.parse_layout(str(Path(self.show_folder) / LAYOUT_NAME))
            except Exception as exc:
                debug(1, f"{{red}}xsq: show folder {self.show_folder}: {exc}")
                self.layout = None
        self.media_found = find_media(self.seq["info"]["media"], self.path, self.show_folder)

    # ------------------------------------------------------------------ loop settings
    def tolerance_frames(self) -> int:
        try:
            n = int(get_preference(PREF_TOLERANCE, DEFAULT_TOLERANCE_FRAMES))
        except (TypeError, ValueError):
            n = DEFAULT_TOLERANCE_FRAMES
        return max(0, min(MAX_TOLERANCE_FRAMES, n))

    def tolerance_ms(self) -> int:
        return self.tolerance_frames() * (self.seq["info"].get("frame_ms") or 50)

    def _apply_tolerance(self):
        self.seq["_tol_ms"] = self.tolerance_ms()

    def patterns(self) -> List[str]:
        value = get_preference(PREF_EXCLUDE, []) or []
        return [p for p in value if isinstance(p, str) and p.strip()]

    def skip_no_controller(self) -> bool:
        return bool(get_preference(PREF_SKIP_NO_CONTROLLER, False))

    def excluded(self) -> set:
        return excluded_rows(self.seq, self.patterns(), self.skip_no_controller(), self.layout)

    def apply_settings(self, tolerance_frames=None, patterns=None, skip_no_controller=None):
        """Save Loop settings; the list and Same as follow at once, and a
        loop report already shown is worked out again."""
        if tolerance_frames is not None:
            set_preference(PREF_TOLERANCE, max(0, min(MAX_TOLERANCE_FRAMES, int(tolerance_frames))))
        if patterns is not None:
            set_preference(PREF_EXCLUDE, list(patterns))
        if skip_no_controller is not None:
            set_preference(PREF_SKIP_NO_CONTROLLER, bool(skip_no_controller))
        self._apply_tolerance()
        self._loops = None
        self.refresh()
        self.show_summary()
        if self._report_shown:
            self.find_loops()

    def set_excluded(self, keys, excluded: bool):
        """Right-click: leave rows out of loop checking (or check them
        again). A whole element is added by its exact name; a submodel or
        strand as "Element / Part"."""
        pats = self.patterns()
        for key in keys:
            pat = glob_escape(row_label(key))
            if excluded:
                if pat not in pats:
                    pats.append(pat)
            else:
                label = row_label(key)
                pats = [p for p in pats if not (_matches_pattern(label, p) and p == glob_escape(label))]
        self.apply_settings(patterns=pats)
        left = [k for k in keys if k in self.excluded()] if not excluded else []
        if left:   # still left out by a wildcard or the no-controller setting
            self.status_var.set("Still left out by a pattern or the no-controller setting: see Loop settings...")

    def selected_rows(self) -> List[Tuple[str, str]]:
        keys = []
        for iid in self.tree.selection():
            if iid.startswith("e:"):
                keys.append((iid[2:], ""))
            elif iid.startswith("p:"):
                element, part = iid[2:].split("/", 1)
                keys.append((element, part))
        return keys

    def _context_menu(self, event):
        iid = self.tree.identify_row(event.y)
        if not iid:
            return
        if iid not in self.tree.selection():
            self.tree.selection_set((iid,))
        keys = self.selected_rows()
        if not keys:
            return
        excluded = self.excluded()
        menu = tk.Menu(self.tree, tearoff=False, bg="#ffffff", fg=FG, activebackground=SEL_BG,
                       activeforeground=SEL_FG, disabledforeground=EXCLUDED_FG)
        what = row_label(keys[0]) if len(keys) == 1 else f"{len(keys)} rows"
        menu.add_command(label=f"Leave {what} out of loop checking",
                         command=lambda: self.set_excluded(keys, True),
                         state="normal" if any(k not in excluded for k in keys) else "disabled")
        menu.add_command(label=f"Check {what} for loops again",
                         command=lambda: self.set_excluded(keys, False),
                         state="normal" if any(k in excluded for k in keys) else "disabled")
        menu.add_separator()
        menu.add_command(label="Loop settings...", command=self.loop_settings_dialog)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                menu.grab_release()
            except tk.TclError:
                pass
        self._menu = menu

    def loop_settings_dialog(self):
        """Tolerance (frames), skip models with no controller, and the list
        of names left out of loop checking."""
        top = tk.Toplevel(self.canvas)
        top.title("Loop settings")
        top.configure(bg=BG)
        try:
            top.transient(self.canvas.winfo_toplevel())
        except tk.TclError:
            pass
        pad = {"padx": 10, "pady": (6, 0)}
        fms = self.seq["info"].get("frame_ms") or 50
        row = tk.Frame(top, bg=BG)
        row.pack(fill="x", **pad)
        tk.Label(row, text="Times may differ by up to", bg=BG, fg=FG).pack(side="left")
        tol_var = tk.StringVar(value=str(self.tolerance_frames()))
        spin = tk.Spinbox(row, from_=0, to=MAX_TOLERANCE_FRAMES, width=3, textvariable=tol_var, bg=FIELD_BG, fg=FG,
                          buttonbackground="#e2e2e2", insertbackground=FG, relief="solid", bd=1)
        spin.pack(side="left", padx=4)
        ms_var = tk.StringVar()
        tk.Label(row, textvariable=ms_var, bg=BG, fg=FG).pack(side="left")
        nocon_var = tk.BooleanVar(value=self.skip_no_controller())
        cb = tk.Checkbutton(top, text="Leave out models with no controller (and groups of only those)",
                            variable=nocon_var, bg=BG, fg=FG, activebackground=BG, activeforeground=FG,
                            selectcolor=FIELD_BG, highlightthickness=0,
                            disabledforeground=EXCLUDED_FG, state="normal" if self.layout else "disabled")
        cb.pack(anchor="w", **pad)
        if not self.layout:
            tk.Label(top, text="   (needs the show folder: Show folder...)", bg=BG, fg=FG_DIM).pack(anchor="w", padx=10)
        tk.Label(top, text="Leave out these models / groups -- one per line; * and ? are wildcards;\n"
                           "\u201cModel / Submodel\u201d for one part; # starts a comment:",
                 bg=BG, fg=FG, justify="left").pack(anchor="w", **pad)
        box = tk.Text(top, width=52, height=10, bg=FIELD_BG, fg=FG, insertbackground=FG, selectbackground=SEL_BG,
                      selectforeground=SEL_FG, relief="solid", bd=1, wrap="none", undo=True)
        box.pack(fill="both", expand=True, padx=10, pady=(4, 0))
        box.insert("1.0", "\n".join(self.patterns()))
        count_var = tk.StringVar()
        tk.Label(top, textvariable=count_var, bg=BG, fg=FG_DIM).pack(anchor="w", padx=10, pady=(4, 0))

        def frames():
            try:
                return max(0, min(MAX_TOLERANCE_FRAMES, int(tol_var.get())))
            except ValueError:
                return self.tolerance_frames()

        def update(_e=None):
            n = frames()
            ms_var.set(f"frame{'' if n == 1 else 's'} ({n * fms} ms) to still match (nudges)")
            pats = parse_patterns(box.get("1.0", "end"))
            left = excluded_rows(self.seq, pats, nocon_var.get(), self.layout)
            count_var.set(f"{len({k[0] for k in left})} of {len(self.seq['elements'])} models/groups left out")
        for w, seq in ((box, "<KeyRelease>"), (spin, "<KeyRelease>")):
            w.bind(seq, update)
        spin.configure(command=update)
        cb.configure(command=update)
        update()

        def ok():
            self.apply_settings(frames(), parse_patterns(box.get("1.0", "end")), nocon_var.get())
            top.destroy()
        buttons = tk.Frame(top, bg=BG)
        buttons.pack(fill="x", padx=10, pady=8)
        for text, cmd in (("Cancel", top.destroy), ("OK", ok)):
            tk.Button(buttons, text=text, command=cmd, width=8, bg="#e2e2e2", fg=FG, activebackground="#cfe0ff",
                      activeforeground=FG, relief="flat").pack(side="right", padx=(6, 0))
        top.bind("<Escape>", lambda e: top.destroy())
        self._settings = {"top": top, "tolerance": tol_var, "no_controller": nocon_var, "box": box,
                          "count": count_var, "ok": ok}
        return top

    def choose_show_folder(self, folder=None):
        if folder is None:
            folder = filedialog.askdirectory(title="xLights show folder (with xlights_rgbeffects.xml)",
                                             initialdir=self.show_folder or str(Path(self.path).parent))
            if not folder:
                return False
        if not (Path(folder) / LAYOUT_NAME).is_file():
            self.status_var.set(f"No {LAYOUT_NAME} in {folder}")
            return False
        set_preference(PREF_SHOW_FOLDER, str(folder))
        self.load_layout()
        self.refresh()
        self.show_summary()
        return True

    # ------------------------------------------------------------------ building
    def _build(self):
        for attr in ("_plugin_toolbars", "_waveform_toolbars"):
            for w in getattr(self.canvas, attr, None) or []:
                try:
                    w.destroy()
                except tk.TclError:
                    pass
        try:
            style = ttk.Style()
            style.configure("Xsq.Treeview", background=FIELD_BG, fieldbackground=FIELD_BG, foreground=FG,
                            rowheight=20)
            style.map("Xsq.Treeview", background=[("selected", SEL_BG)], foreground=[("selected", SEL_FG)])
            style.configure("Xsq.Treeview.Heading", foreground=FG)
        except (tk.TclError, AttributeError):
            pass
        root = tk.Frame(self.canvas, bg=BG)
        root.place(x=0, y=0, relwidth=1, relheight=1)
        self.frame = root

        bar = tk.Frame(root, bg=BG, padx=4, pady=3)
        bar.pack(side="top", fill="x")
        tk.Label(bar, text="Filter:", bg=BG, fg=FG).pack(side="left")
        self.filter_column = tk.StringVar(value=ANY_COLUMN)
        col_box = ttk.Combobox(bar, textvariable=self.filter_column, state="readonly", width=11,
                               values=[ANY_COLUMN] + [HEADINGS[c] for c in COLUMNS])
        col_box.pack(side="left", padx=(4, 2))
        col_box.bind("<<ComboboxSelected>>", lambda e: self.refresh())
        self.filter_text = tk.StringVar(value="")
        entry = tk.Entry(bar, textvariable=self.filter_text, width=24, bg=FIELD_BG, fg=FG, insertbackground=FG,
                         selectbackground=SEL_BG, selectforeground=SEL_FG, relief="solid", bd=1)
        entry.pack(side="left", padx=2)
        entry.bind("<KeyRelease>", lambda e: self.refresh())
        entry.bind("<Escape>", lambda e: self.clear_filter())
        self.filter_entry = entry
        tk.Button(bar, text="\u2715", command=self.clear_filter, bg="#e2e2e2", fg=FG, activebackground="#cfe0ff",
                  activeforeground=FG, relief="flat", padx=4, pady=0, cursor="hand2").pack(side="left", padx=(0, 10))
        self.only_fx = tk.BooleanVar(value=bool(get_preference("xsq_only_effects", False)))
        tk.Checkbutton(bar, text="Only with effects", variable=self.only_fx, command=self._toggle_only_fx,
                       bg=BG, fg=FG, activebackground=BG, activeforeground=FG, selectcolor=FIELD_BG,
                       highlightthickness=0).pack(side="left")
        tk.Button(bar, text="Show folder...", command=self.choose_show_folder, bg="#e2e2e2", fg=FG,
                  activebackground="#cfe0ff", activeforeground=FG, relief="flat", padx=6, pady=0,
                  cursor="hand2").pack(side="left", padx=(10, 0))
        tk.Button(bar, text="File order", command=self.file_order, bg="#e2e2e2", fg=FG,
                  activebackground="#cfe0ff", activeforeground=FG, relief="flat", padx=6, pady=0,
                  cursor="hand2").pack(side="left", padx=(6, 0))
        self.loops_btn = tk.Button(bar, text="Find loops", command=self.find_loops, bg="#e2e2e2", fg=FG,
                                   activebackground="#cfe0ff", activeforeground=FG, relief="flat", padx=6, pady=0,
                                   cursor="hand2")
        self.loops_btn.pack(side="left", padx=(6, 0))
        tk.Button(bar, text="Loop settings...", command=self.loop_settings_dialog, bg="#e2e2e2", fg=FG,
                  activebackground="#cfe0ff", activeforeground=FG, relief="flat", padx=6, pady=0,
                  cursor="hand2").pack(side="left", padx=(6, 0))
        self.count_var = tk.StringVar(value="")
        tk.Label(bar, textvariable=self.count_var, bg=BG, fg=FG).pack(side="left", padx=(10, 0))
        self.status_var = tk.StringVar(value="")
        tk.Label(bar, textvariable=self.status_var, bg=BG, fg=FG_DIM).pack(side="right")

        body = tk.Frame(root, bg=BG)
        body.pack(side="top", fill="both", expand=True)
        tree = ttk.Treeview(body, style="Xsq.Treeview", columns=COLUMNS[1:], selectmode="extended")
        tree.heading("#0", text=HEADINGS["element"], command=lambda: self.sort_by("element"))
        tree.column("#0", width=230, stretch=False)
        widths = {"kind": 96, "effects": 64, "own": 52, "parts": 80, "layers": 56, "visible": 56, "types": 230,
                  "same": 220}
        for col in COLUMNS[1:]:
            tree.heading(col, text=HEADINGS[col], command=lambda c=col: self.sort_by(c))
            tree.column(col, width=widths[col], stretch=(col in ("types", "same")),
                        anchor="e" if col in NUMERIC else ("center" if col == "visible" else "w"))
        tree.tag_configure("even", background=ROW_BG)
        tree.tag_configure("odd", background=ROW_ALT_BG)
        tree.tag_configure("empty", foreground=EMPTY_FG)
        tree.tag_configure("part", foreground=FG_DIM, font=("TkDefaultFont", 9, "italic"))
        tree.tag_configure("excluded", foreground=EXCLUDED_FG, font=("TkDefaultFont", 9, "overstrike"))
        tree.bind("<Button-3>", self._context_menu)
        ysb = ttk.Scrollbar(body, orient="vertical", command=tree.yview)
        xsb = ttk.Scrollbar(body, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)
        ysb.pack(side="right", fill="y")
        xsb.pack(side="bottom", fill="x")
        tree.pack(side="left", fill="both", expand=True)
        tree.bind("<Escape>", lambda e: tree.selection_set(()))
        self.tree = tree
        self.grid = xl.GridLines(tree)
        self.grid.hook_scrollbars(yset=ysb.set, xset=xsb.set)
        self._update_headings()

    def min_panel_height(self):
        return 120

    def preferred_panel_height(self):
        return 420

    # ------------------------------------------------------------------ content
    def show_summary(self):
        if self.text is None:
            return
        try:
            self.text.configure(state="normal")
            self.text.delete("1.0", "end")
            insert_styled_text(self.text, xsq_summary(self.path, self.seq, self.show_folder, self.layout,
                                                      self.media_found))
            self.text.edit_modified(False)
        except tk.TclError:
            pass

    def rows(self):
        self._same = same_as_map(copies_of(self.seq))
        return element_rows(self.seq, self.layout)

    # ------------------------------------------------------------------ loops
    def find_loops(self):
        """Search in the background (big sequences take a few seconds);
        the report goes under the summary in the text panel."""
        if getattr(self, "_loop_thread", None) is not None:
            return False
        if getattr(self, "_loops", None) is not None:
            self._show_loops()
            return True
        self.status_var.set("Looking for loops and copied rows...")
        try:
            self.loops_btn.configure(state="disabled")
        except (tk.TclError, AttributeError):
            pass
        box: Dict[str, Any] = {}
        duration = self.seq["info"]["duration"]
        duration_ms = int(round(duration * 1000)) if duration else None
        tol, exclude = self.tolerance_ms(), self.excluded()
        self._loop_settings = (tol, exclude)

        def work():
            t0 = time.time()
            try:
                box["result"] = find_loops(self.seq, duration_ms=duration_ms, tol_ms=tol, exclude=exclude)
            except Exception as exc:          # report it in the panel, don't lose it in the thread
                box["error"] = exc
            box["elapsed"] = time.time() - t0
        self._loop_thread = threading.Thread(target=work, daemon=True)
        self._loop_thread.start()

        def poll():
            if self._loop_thread.is_alive():
                self.canvas.after(100, poll)
                return
            self._loop_thread = None
            try:
                self.loops_btn.configure(state="normal")
            except (tk.TclError, AttributeError):
                pass
            if "error" in box:
                debug(1, f"{{red}}xsq: loop search failed: {box['error']}")
                self.status_var.set(f"Loop search failed: {box['error']}")
                return
            self._loops = box["result"]
            debug(2, f"xsq: loops in {box['elapsed']:.2f}s")
            self._show_loops()
        self.canvas.after(100, poll)
        return True

    def _show_loops(self):
        found = self._loops
        copies = copies_of(self.seq)
        n_l, n_p = len(found["loops"]), len(found["passages"])
        self.status_var.set(f"{n_l} loop{'' if n_l == 1 else 's'}, {n_p} repeated passage{'' if n_p == 1 else 's'}, "
                            f"{len(copies)} copied set{'' if len(copies) == 1 else 's'}")
        self._report_shown = True
        if self.text is None:
            return
        tol, exclude = getattr(self, "_loop_settings", (0, set()))
        try:
            self.show_summary()
            self.text.configure(state="normal")
            insert_styled_text(self.text, loops_report(self.seq, found, copies, excluded=exclude, tol_ms=tol))
            self.text.edit_modified(False)
        except tk.TclError:
            pass

    def _filter_key(self):
        label = self.filter_column.get()
        return next((c for c in COLUMNS if HEADINGS[c] == label), ANY_COLUMN)

    def refresh(self):
        rows = filter_rows(self.rows(), self._filter_key(), self.filter_text.get(), self.only_fx.get())
        rows = sort_rows(rows, self.sort_column, self.sort_reverse,
                         bool(get_preference(xl.PREF_SORT_CASE, True)))
        self.shown = rows
        tree = self.tree
        tree.delete(*tree.get_children())
        excluded = self.excluded()
        for i, r in enumerate(rows):
            tags = ["even" if i % 2 == 0 else "odd"] + ([] if r["effects"] else ["empty"])
            if (r["element"], "") in excluded or (not r["effects"] and r["element"] in {k[0] for k in excluded}):
                tags.append("excluded")
            iid = "e:" + r["element"]
            tree.insert("", "end", iid=iid, text=r["element"], tags=tuple(tags),
                        values=(r["kind"], r["effects"], r["own"], r["parts"] or "", r["layers"],
                                visible_text(r["visible"]), r["types"], r["same"]))
            parts = self.seq["elements"][r["element"]]["parts"]
            same = self._same
            for part, n in parts.items():
                ptags = ("part", "excluded") if (r["element"], part) in excluded else ("part",)
                tree.insert(iid, "end", iid=f"p:{r['element']}/{part}", text=part, tags=ptags,
                            values=("submodel" if not part.startswith("Strand ") else
                                    ("node" if "/ Node" in part else "strand"), n, "", n, "", "", "",
                                    same_as_text((r["element"], part), same)))
        total = len(self.seq["elements"])
        self.count_var.set(f"{len(rows)} of {total} shown")
        try:
            self.grid.schedule()
        except (tk.TclError, AttributeError):
            pass

    def _update_headings(self):
        for col in COLUMNS:
            arrow = ""
            if col == self.sort_column:
                arrow = " \u25bc" if self.sort_reverse else " \u25b2"
            self.tree.heading("#0" if col == "element" else col, text=HEADINGS[col] + arrow)

    def sort_by(self, column):
        if column == self.sort_column:
            self.sort_reverse = not self.sort_reverse
        else:
            self.sort_column, self.sort_reverse = column, column in NUMERIC   # counts: most first
        self._update_headings()
        self.refresh()

    def file_order(self):
        self.sort_column, self.sort_reverse = None, False
        self._update_headings()
        self.refresh()

    def set_filter(self, column, spec):
        self.filter_column.set(HEADINGS.get(column, ANY_COLUMN))
        self.filter_text.set(spec)
        self.refresh()

    def clear_filter(self):
        self.filter_text.set("")
        self.refresh()

    def _toggle_only_fx(self):
        set_preference("xsq_only_effects", bool(self.only_fx.get()))
        self.refresh()
