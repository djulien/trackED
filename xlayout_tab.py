"""
xlayout_tab.py -- trackED plugin for an xLights layout file
(xlights_rgbeffects.xml, or any .xml whose root is <xrgb>).

Read-only view of the layout's model groups and models, plus two values
of your own per model -- a style and a comment -- kept in trackED's
sidecar file next to the layout ("<stem>-tracked.json", section
"model_notes"), for use later together with the timing tracks. The layout
file itself is never written.

  text panel  a summary: model and group counts, nodes, models by type,
              group nesting, unknown group members
  left        the group tree: nested groups can be expanded/collapsed;
              select one or more groups (Ctrl/Shift+click) to list only
              their models. "(not in any group)" lists the rest.
  separator   drag it to resize the two panes (remembered)
  right       the models: Model, Type, Nodes, Preview, Master, Style,
              Comment. Click a heading to sort (again: reverse); the group
              tree sorts the same way (Groups, Models, Preview, Master).
              Sorting is alphabetical, case-sensitive unless turned off in
              Preferences, with numbers in numeric order. Filter by one
              column (or any) with the box above the list. With groups
              selected, models that are only in a nested group (not a
              direct member) are shown in gray italics.
              Selecting a model highlights the groups it's in (direct
              members: yellow; only via nested groups: pale yellow italic),
              opening the tree down to them.
              Double-click a Style or Comment cell to edit it; right-click
              for "set for all selected" and "filter by this value".
              File > Save (or auto-save) writes the notes to the sidecar.

Filter syntax: text matches anywhere (case-insensitive); "=text" matches
the whole value ("=" alone: empty); "!text" excludes. Nodes also take
">100", ">=50", "<10", "=0" and ranges "10-50".

Node counts are computed from each model's settings (strings x nodes per
string for most types, the grid for Custom models, top+2*sides+bottom for
a Window Frame, ...): exact for the common types, "?" where the type
isn't known, blank for DMX / image / label models.

Master: a check mark for models/groups listed in the layout's
<view name="Master View" models="..."> element (the Master View as xLights
last saved it in the layout); if the file has no such
list the column stays empty (the summary says so). Preview: the model's
LayoutGroup ("Default" when unset). Both panels have alternating row
colors and faint cell borders (GridLines: 1-pixel frames over the
Treeview, which has no grid of its own).

The pure layout logic (parse_layout, groups_to_models, filter/sort) needs
no Tk and is unit-tested in tests.py.
"""

from __future__ import annotations

import copy
import re
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import tkinter as tk
from tkinter import ttk, simpledialog

from utils import debug, get_preference, insert_styled_text, set_preference

import timing_helpers as th

LAYOUT_EXTS = {".xml"}
FILE_TYPES = [("xLights layout", "*.xml")]   # File > Open (tracked.py)
NOTES_KEY = "model_notes"          # section of the sidecar file
COLUMNS = ("model", "type", "nodes", "preview", "master", "style", "comment")
HEADINGS = {"model": "Model", "type": "Type", "nodes": "Nodes", "preview": "Preview", "master": "Master",
            "style": "Style", "comment": "Comment"}
GROUP_COLUMNS = ("group", "count", "preview", "master")      # "group" is the tree column (#0)
GROUP_HEADINGS = {"group": "Groups", "count": "Models", "preview": "Preview", "master": "Master"}
MASTER_VIEW_NAMES = ("master view", "master")
MASTER_MARK = "\u2713"
PREF_SORT_CASE = "xlayout_sort_case"      # Preferences: case-sensitive sorting (default on)
EDITABLE = ("style", "comment")
ANY_COLUMN = "Any column"
UNGROUPED = "(not in any group)"
UNDO_LIMIT = 200

# Explicit colors everywhere (the desktop theme's default text is light).
FG = "#1e1e1e"
FG_DIM = "#8a8a8a"
BG = "#f2f2f2"
FIELD_BG = "#ffffff"
SEL_BG = "#264f78"
SEL_FG = "#ffffff"
SASH_BG = "#c8c8c8"
ROW_BG = "#ffffff"
ROW_ALT_BG = "#f3f6fa"        # alternate rows
HL_DIRECT_BG = "#ffe08a"      # groups the selected model is directly in
HL_INDIRECT_BG = "#fff3cc"    # ...only through a nested group
GRID_COLOR = "#e1e4e8"        # faint cell borders


# ===========================================================================
# Pure logic (no Tk)
# ===========================================================================

def is_layout_file(path: str) -> bool:
    """An .xml file whose root element is <xrgb> (xLights' layout file)."""
    p = Path(path)
    if p.suffix.lower() not in LAYOUT_EXTS or not p.is_file():
        return False
    try:
        with open(p, "rb") as f:
            head = f.read(4096)
    except OSError:
        return False
    return re.search(rb"<xrgb[\s>/]", head) is not None


def _int(attrs: Dict[str, str], key: str) -> int:
    try:
        return int(float(attrs.get(key, 0) or 0))
    except (TypeError, ValueError):
        return 0


def _custom_nodes(attrs: Dict[str, str]) -> Optional[int]:
    """Distinct node numbers in a Custom model's grid (CustomModel:
    cells "," / rows ";" / layers "|"; or CustomModelCompressed:
    "node,row,col[,layer];...")."""
    nodes = set()
    compressed = attrs.get("CustomModelCompressed")
    if compressed:
        for entry in compressed.split(";"):
            first = entry.split(",")[0].strip()
            if first.isdigit():
                nodes.add(int(first))
    else:
        for cell in re.split(r"[,;|]", attrs.get("CustomModel", "")):
            cell = cell.strip()
            if cell.isdigit():
                nodes.add(int(cell))
    return len(nodes) if nodes or "CustomModel" in attrs or compressed else None


_STRINGS_X_NODES = ("arches", "candy canes", "circle", "icicles", "single line", "poly line", "star",
                    "wreath", "sphere", "multipoint")


def node_count(attrs: Dict[str, str]) -> Optional[int]:
    """Number of nodes of one <model>, from its DisplayAs and parm1..3.
    None when the type has no nodes to speak of (DMX, image, label) or
    isn't known."""
    kind = (attrs.get("DisplayAs") or "").strip().lower()
    p1, p2, p3 = _int(attrs, "parm1"), _int(attrs, "parm2"), _int(attrs, "parm3")
    if kind == "custom":
        return _custom_nodes(attrs)
    if kind.startswith("dmx") or kind in ("image", "label", "ruler"):
        return None
    if kind == "window frame":
        return p1 + 2 * p2 + p3                 # top + both sides + bottom
    if kind == "channel block":
        return p1
    if kind in ("cube", "spinner"):
        return p1 * p2 * p3
    if kind in _STRINGS_X_NODES or kind.startswith("tree") or "matrix" in kind:
        if (attrs.get("StringType") or "").lower().startswith("single color"):
            return p1                           # one node per string
        return p1 * p2
    return p1 * p2 if p1 and p2 else None


def nodes_text(nodes: Optional[int], kind: str) -> str:
    """Nodes column text: "1,200"; blank for types without nodes (DMX,
    image, label); "?" when the type isn't known."""
    if nodes is not None:
        return f"{nodes:,}"
    k = (kind or "").lower()
    return "" if k.startswith("dmx") or k in ("image", "label", "ruler") else "?"


def parse_layout(path: str) -> Dict[str, Any]:
    """Read an xLights layout file:
    {"models": {name: {"name", "type", "nodes", "string_type", "submodels"}},
     "groups": {name: {"name", "members": [raw names], "models": [direct
                model names], "groups": [child group names], "unknown": [...]}},
     "model_order": [...], "group_order": [...]}
    A group member "Model/SubModel" counts as that model. Also each
    model's/group's preview (LayoutGroup, "Default" if unset) and the
    layout's <view name=... models=...> lists ("views"), from which the
    Master View membership is taken ("master": a set, or None)."""
    root = ET.parse(path).getroot()
    if root.tag != "xrgb":
        raise ValueError(f"not an xLights layout file (root <{root.tag}>)")
    models: Dict[str, Dict[str, Any]] = {}
    for el in root.iter("model"):
        name = (el.get("name") or "").strip()
        if not name or name in models:
            continue
        attrs = dict(el.attrib)
        models[name] = {
            "name": name,
            "type": attrs.get("DisplayAs", ""),
            "nodes": node_count(attrs),
            "string_type": attrs.get("StringType", ""),
            "preview": attrs.get("LayoutGroup") or "Default",
            "submodels": [s.get("name", "") for s in el.findall("subModel")],
        }
    groups: Dict[str, Dict[str, Any]] = {}
    for el in root.iter("modelGroup"):
        name = (el.get("name") or "").strip()
        if not name or name in groups:
            continue
        members = [m.strip() for m in (el.get("models") or "").split(",") if m.strip()]
        groups[name] = {"name": name, "members": members, "models": [], "groups": [], "unknown": [],
                        "preview": el.get("LayoutGroup") or "Default"}
    for g in groups.values():
        for member in g["members"]:
            if member in groups and member != g["name"]:
                if member not in g["groups"]:
                    g["groups"].append(member)
            elif member in models:
                if member not in g["models"]:
                    g["models"].append(member)
            elif "/" in member and member.split("/", 1)[0] in models:
                base = member.split("/", 1)[0]       # a submodel (or strand) of a model
                if base not in g["models"]:
                    g["models"].append(base)
            else:
                g["unknown"].append(member)
    views: Dict[str, List[str]] = {}
    for el in root.iter("view"):
        vname = (el.get("name") or "").strip()
        if vname and vname not in views:
            views[vname] = [m.strip() for m in (el.get("models") or "").split(",") if m.strip()]
    master_name = next((v for v in views if v.strip().lower() in MASTER_VIEW_NAMES), None)
    return {"models": models, "groups": groups,
            "model_order": list(models), "group_order": list(groups),
            "views": views,
            # names (models and groups) in the Master View, or None if the
            # file has no Master View list
            "master": set(views[master_name]) if master_name is not None else None}


def in_master(layout: Dict[str, Any], name: str) -> Optional[bool]:
    """Is this model/group in the Master View? None if unknown."""
    master = layout.get("master")
    if master is None:
        return None
    return name in master


def group_models(layout: Dict[str, Any], group: str) -> Dict[str, str]:
    """{model: "direct" | "indirect"} for one group: its own members are
    direct, members of its nested groups (at any depth) indirect."""
    groups = layout["groups"]
    out: Dict[str, str] = {}
    if group not in groups:
        return out
    for m in groups[group]["models"]:
        out[m] = "direct"
    seen = {group}
    stack = list(groups[group]["groups"])
    while stack:
        g = stack.pop()
        if g in seen or g not in groups:
            continue
        seen.add(g)
        for m in groups[g]["models"]:
            out.setdefault(m, "indirect")
        stack.extend(groups[g]["groups"])
    return out


def groups_to_models(layout: Dict[str, Any], selected: List[str]) -> Dict[str, str]:
    """Models in any of the selected groups: {model: "direct"|"indirect"};
    direct in any one of them wins. UNGROUPED selects the models that
    are in no group at all (as direct)."""
    out: Dict[str, str] = {}
    for g in selected:
        found = {m: "direct" for m in ungrouped_models(layout)} if g == UNGROUPED else group_models(layout, g)
        for m, how in found.items():
            if how == "direct" or m not in out:
                out[m] = how
    return out


def groups_containing(layout: Dict[str, Any], models: List[str]) -> Dict[str, str]:
    """The groups these models are in: {group: "direct"|"indirect"} --
    direct if one of the models is the group's own member, indirect if
    only through a nested group. (Several models: direct in any wins.)"""
    wanted = set(models)
    out: Dict[str, str] = {}
    for name in layout["group_order"]:
        found = group_models(layout, name)
        kinds = {found[m] for m in wanted if m in found}
        if "direct" in kinds:
            out[name] = "direct"
        elif kinds:
            out[name] = "indirect"
    return out


def ungrouped_models(layout: Dict[str, Any]) -> List[str]:
    grouped = {m for g in layout["groups"].values() for m in g["models"]}
    return [m for m in layout["model_order"] if m not in grouped]


def top_level_groups(layout: Dict[str, Any]) -> List[str]:
    """Groups that aren't inside another group (plus, so nothing is
    lost, any group only reachable through a cycle)."""
    groups = layout["groups"]
    nested = {c for g in groups.values() for c in g["groups"]}
    tops = [g for g in layout["group_order"] if g not in nested]
    reach, stack = set(), list(tops)
    while stack:
        g = stack.pop()
        if g in reach:
            continue
        reach.add(g)
        stack.extend(groups[g]["groups"])
    return tops + [g for g in layout["group_order"] if g not in reach]


def group_depth(layout: Dict[str, Any]) -> int:
    """Deepest nesting of groups (1 = no group inside another)."""
    groups = layout["groups"]

    def depth(g, trail):
        kids = [c for c in groups[g]["groups"] if c not in trail]
        return 1 + max((depth(c, trail | {c}) for c in kids), default=0)
    return max((depth(g, {g}) for g in groups), default=0)


def natural_key(value: Any, case_sensitive: bool = True) -> Tuple:
    """Sort key: alphabetical, case-sensitive by default (as in xLights:
    "B" before "a"), with numbers in numeric order ("Arch 2" before
    "Arch 10"); None / "" last."""
    if value is None or value == "":
        return (1, ())
    if isinstance(value, (int, float)):
        return (0, ((0, float(value), ""),))
    text = str(value) if case_sensitive else str(value).lower()
    parts = re.split(r"(\d+)", text)
    return (0, tuple((0, float(p), "") if p.isdigit() else (1, 0.0, p) for p in parts if p != ""))


_YES = ("yes", "y", "true", "1", MASTER_MARK, "x", "*")
_NO = ("no", "n", "false", "0", "-")
_NUM_RE = re.compile(r"^(>=|<=|>|<|=)?\s*(-?\d+(?:\.\d+)?)$")
_RANGE_RE = re.compile(r"^(-?\d+(?:\.\d+)?)\s*-\s*(-?\d+(?:\.\d+)?)$")


def matches(value: Any, spec: str, numeric: bool = False) -> bool:
    """Does a cell value match a filter spec (see the module doc)?"""
    spec = (spec or "").strip()
    if not spec:
        return True
    if spec.startswith("!"):
        return not matches(value, spec[1:], numeric) if spec[1:].strip() else True
    if isinstance(value, bool) or (value is None and spec.lower().lstrip("=") in _YES + _NO):
        word = spec.lower().lstrip("=").strip()
        if word in _YES:
            return value is True
        if word in _NO:
            return value is False
        value = MASTER_MARK if value else ""
    if numeric:
        m = _RANGE_RE.match(spec)
        if m:
            return value is not None and float(m.group(1)) <= value <= float(m.group(2))
        m = _NUM_RE.match(spec)
        if m:
            if value is None:
                return False
            op, num = m.group(1) or "=", float(m.group(2))
            return {"=": value == num, ">": value > num, "<": value < num,
                    ">=": value >= num, "<=": value <= num}[op]
    text = "" if value is None else str(value)
    if spec.startswith("="):
        return text.lower() == spec[1:].strip().lower()
    return spec.lower() in text.lower()


def model_rows(layout: Dict[str, Any], notes: Dict[str, Dict[str, str]]) -> List[Dict[str, Any]]:
    rows = []
    for name in layout["model_order"]:
        m = layout["models"][name]
        n = notes.get(name) or {}
        rows.append({"model": name, "type": m["type"], "nodes": m["nodes"], "preview": m["preview"],
                     "master": in_master(layout, name),
                     "style": n.get("style", ""), "comment": n.get("comment", "")})
    return rows


def master_text(value: Optional[bool]) -> str:
    return MASTER_MARK if value else ""


def group_row(layout: Dict[str, Any], name: str) -> Dict[str, Any]:
    """Sortable values of one group (the group tree's columns)."""
    if name == UNGROUPED:
        return {"group": name, "count": len(ungrouped_models(layout)), "preview": "", "master": None}
    g = layout["groups"][name]
    return {"group": name, "count": len(group_models(layout, name)), "preview": g["preview"],
            "master": in_master(layout, name)}


def sort_group_names(layout: Dict[str, Any], names: List[str], column: str = "group", reverse: bool = False,
                     case_sensitive: bool = True) -> List[str]:
    """Order groups (one level of the tree) by a group column."""
    rows = sort_rows([group_row(layout, n) for n in names], column, reverse, case_sensitive, name_key="group")
    return [r["group"] for r in rows]


def filter_rows(rows: List[Dict[str, Any]], column: str, spec: str) -> List[Dict[str, Any]]:
    if not (spec or "").strip():
        return list(rows)
    if column in COLUMNS:
        return [r for r in rows if matches(r[column], spec, numeric=(column == "nodes"))]
    def shown(r, c):          # "any column" compares the text as shown
        return master_text(r[c]) if c == "master" else r[c]
    if spec.strip().startswith("!"):     # "!x" on any column: no column contains x
        return [r for r in rows if all(matches(shown(r, c), spec) for c in COLUMNS)]
    return [r for r in rows if any(matches(shown(r, c), spec) for c in COLUMNS)]


def sort_rows(rows: List[Dict[str, Any]], column: str, reverse: bool = False,
              case_sensitive: bool = True, name_key: str = "model") -> List[Dict[str, Any]]:
    """Stable sort by one column (then by name); empty values stay last in
    either direction. For the Master column, members come first."""
    rows = sorted(rows, key=lambda r: natural_key(r[name_key], case_sensitive))
    if column == "master":             # members first (unknown always last)
        known = [r for r in rows if r["master"] is not None]
        return sorted(known, key=lambda r: 0 if r["master"] else 1, reverse=reverse) + \
            [r for r in rows if r["master"] is None]
    filled = [r for r in rows if r[column] not in (None, "")]
    empty = [r for r in rows if r[column] in (None, "")]
    return sorted(filled, key=lambda r: natural_key(r[column], case_sensitive), reverse=reverse) + empty


def layout_summary(path: str, layout: Dict[str, Any], notes: Dict[str, Dict[str, str]]) -> str:
    """Styled text for the text panel."""
    models, groups = layout["models"], layout["groups"]
    p = Path(path)
    lines = [
        "{cyan}[xlayout_tab]",
        f"{{blue}}xLights layout: {{cyan}}{p.name}",
        f"{{blue}}Path:  {p.resolve()}",
        "",
        f"{{blue}}Models: {{cyan}}{len(models)}"
        + (f"{{blue}}  (+ {sum(len(m['submodels']) for m in models.values())} submodels)"
           if any(m["submodels"] for m in models.values()) else ""),
        f"{{blue}}Groups: {{cyan}}{len(groups)}{{blue}}  ({len(top_level_groups(layout))} top-level, "
        f"nested up to {group_depth(layout)} level{'s' if group_depth(layout) != 1 else ''} deep)",
    ]
    known = [m["nodes"] for m in models.values() if m["nodes"] is not None]
    unknown = [m["name"] for m in models.values() if m["nodes"] is None]
    lines.append(f"{{blue}}Nodes:  {{cyan}}{sum(known):,}"
                 + (f"{{blue}}  ({len(unknown)} model{'s' if len(unknown) != 1 else ''} without a node count)"
                    if unknown else ""))
    previews: Dict[str, int] = {}
    for m in models.values():
        previews[m["preview"]] = previews.get(m["preview"], 0) + 1
    lines.append("{blue}Previews: " + ", ".join(f"{{cyan}}{name}{{blue}} ({n})" for name, n in
                                                sorted(previews.items(), key=lambda kv: natural_key(kv[0]))))
    if layout.get("master") is None:
        lines.append("{yellow}Master View: no <view name=\"Master View\"> list found in this file "
                     "(the Master column stays empty)")
    else:
        mm = sum(1 for n in models if n in layout["master"])
        mg = sum(1 for n in groups if n in layout["master"])
        lines.append(f"{{blue}}Master View: {{cyan}}{mm}{{blue}} models, {{cyan}}{mg}{{blue}} groups")
    loose = ungrouped_models(layout)
    lines.append(f"{{blue}}Not in any group: {{cyan}}{len(loose)}{{blue}} model{'s' if len(loose) != 1 else ''}")
    noted = sum(1 for n in notes.values() if n.get("style") or n.get("comment"))
    lines.append(f"{{blue}}With a style or comment: {{cyan}}{noted}")
    by_type: Dict[str, List[int]] = {}
    for m in models.values():
        by_type.setdefault(m["type"] or "?", []).append(m["nodes"] or 0)
    if by_type:
        lines.append("")
        lines.append("{blue}Models by type:")
        for kind, nodes in sorted(by_type.items(), key=lambda kv: (-len(kv[1]), kv[0].lower())):
            lines.append(f"{{blue}}  {kind:<16} {{cyan}}{len(nodes):4d}{{blue}}   {sum(nodes):,} nodes")
    missing = [(g["name"], u) for g in groups.values() for u in g["unknown"]]
    if missing:
        lines.append("")
        lines.append(f"{{yellow}}Group members not found in the layout ({len(missing)}):")
        for gname, member in missing[:20]:
            lines.append(f"{{yellow}}  {gname}: {member}")
        if len(missing) > 20:
            lines.append(f"{{yellow}}  ... and {len(missing) - 20} more")
    lines += [
        "",
        "{blue}Groups (left): {cyan}click{blue} a group to list its models, {cyan}Ctrl/Shift+click{blue} "
        "for several; {cyan}Esc{blue} or {cyan}Clear{blue} shows all",
        "{blue}   models only in a nested group (not direct members) are {cyan}gray italic",
        "{blue}Models (right): {cyan}click a heading{blue} to sort; the {cyan}Filter{blue} box filters by a column: "
        "text, {cyan}=exact{blue}, {cyan}!exclude{blue}; Nodes also {cyan}>100{blue}, {cyan}10-50",
        "{blue}   {cyan}double-click{blue} a Style or Comment cell to edit it; {cyan}right-click{blue} to set it "
        "for all selected models or to filter by a value",
        f"{{blue}}Style and comment are saved (File > Save / auto-save) to {{cyan}}{Path(th.cache_path(path)).name}"
        "{blue}; the layout file is never changed.",
    ]
    return "\n".join(lines) + "\n"


def grid_positions(cells: List[Tuple[int, int, int, int]], height: int) -> Tuple[List[int], List[int]]:
    """Where to draw the faint cell borders, from the bboxes (x, y, w, h)
    of the first visible row's cells: a vertical line at each cell's
    right edge, and horizontal lines every row height from that row's top
    down to `height`."""
    if not cells:
        return [], []
    xs = sorted({x + w - 1 for x, _y, w, _h in cells if w > 0})
    _x, top, _w, row_h = cells[0]
    ys = list(range(top - 1, height, row_h)) if row_h > 0 else []
    return xs, [y for y in ys if y >= 0]


class GridLines:
    """Faint cell borders over a ttk.Treeview (it can't draw its own):
    1-pixel frames at the column edges and row boundaries of the visible
    area, redrawn (debounced) when the tree is resized, scrolled, its
    columns are resized, or its rows change."""

    def __init__(self, tree, color: str = GRID_COLOR):
        self.tree, self.color = tree, color
        self.lines: List[Any] = []
        self._pending = False
        for seq in ("<Configure>", "<B1-Motion>", "<ButtonRelease-1>", "<MouseWheel>", "<Button-4>",
                    "<Button-5>", "<KeyRelease>"):
            tree.bind(seq, lambda e: self.schedule(), add="+")

    def hook_scrollbars(self, yset=None, xset=None):
        """Call after configuring the tree's scrollbars: route their
        updates through here so scrolling redraws the lines."""
        def make(setter):
            def on_scroll(first, last):
                setter(first, last)
                self.schedule()
            return on_scroll
        if yset is not None:
            self.tree.configure(yscrollcommand=make(yset))
        if xset is not None:
            self.tree.configure(xscrollcommand=make(xset))

    def schedule(self):
        if self._pending:
            return
        self._pending = True
        try:
            self.tree.after_idle(self.redraw)
        except (tk.TclError, AttributeError):
            self.redraw()

    def _first_visible(self):
        tree = self.tree
        for y in range(1, 120, 3):
            try:
                iid = tree.identify_row(y)
            except tk.TclError:
                return None
            if iid and isinstance(iid, str):
                return iid
        return None

    def redraw(self):
        self._pending = False
        tree = self.tree
        try:
            iid = self._first_visible()
            cells = []
            if iid:
                shown = tree["displaycolumns"]
                cols = list(tree["columns"]) if shown in ("#all", ("#all",)) else list(shown)
                if "tree" in str(tree.cget("show")):
                    cols = ["#0"] + cols
                for col in cols:
                    box = tree.bbox(iid, col)
                    if box:
                        cells.append(tuple(int(v) for v in box))
            width, height = int(tree.winfo_width()), int(tree.winfo_height())
        except (tk.TclError, TypeError, ValueError):
            return
        xs, ys = grid_positions(cells, height)
        top = cells[0][1] if cells else 0
        needed = [("v", x) for x in xs] + [("h", y) for y in ys]
        while len(self.lines) < len(needed):
            self.lines.append(tk.Frame(tree, bg=self.color, bd=0, highlightthickness=0))
        for line, (kind, pos) in zip(self.lines, needed):
            if kind == "v":
                line.place(x=pos, y=top, width=1, height=max(0, height - top))
            else:
                line.place(x=0, y=pos, width=width, height=1)
        for line in self.lines[len(needed):]:
            line.place_forget()
        self.positions = needed


# ===========================================================================
# Plugin entry point
# ===========================================================================

def onload(filepath: str, canvas=None, text=None, tab=None):
    if not is_layout_file(filepath):
        return False
    if canvas is None:
        return True                     # probe only
    path = str(Path(filepath).resolve())
    try:
        layout = parse_layout(path)
    except Exception as exc:            # a broken file: say so instead of failing silently
        debug(1, f"{{red}}xlayout: {path}: {exc}")
        if text is not None:
            text.delete("1.0", "end")
            insert_styled_text(text, f"{{cyan}}[xlayout_tab]\n{{red}}Couldn't read {Path(path).name}: {exc}\n")
        if tab is not None:
            tab.protect_file = True
        return True
    view = LayoutView(canvas, path, layout, tab=tab, text=text)
    canvas._layout_view = view          # keep it alive
    if tab is not None:
        tab.protect_file = True         # the text panel is a summary: never saved over the layout
        tab.min_sash = view.min_panel_height
        tab.preferred_sash = view.preferred_panel_height
        tab.save_hook = view.save
        tab.undo_hook = view.undo
        tab.redo_hook = view.redo
        tab.title_detail = f"{len(layout['models'])} models, {len(layout['groups'])} groups"
    view.show_summary()
    debug(1, f"{{green}}xlayout: {path}: {len(layout['models'])} models, {len(layout['groups'])} groups")
    return True


# ===========================================================================
# The view (Tk)
# ===========================================================================

class LayoutView:
    """Group tree | movable separator | model list, over the tab's canvas."""

    def __init__(self, canvas, path: str, layout: Dict[str, Any], tab=None, text=None):
        self.canvas = canvas
        self.path = path
        self.layout = layout
        self.tab = tab
        self.text = text
        cached = th.load_cache(path).get(NOTES_KEY) or {}
        self.notes: Dict[str, Dict[str, str]] = {k: dict(v) for k, v in cached.items()
                                                 if isinstance(v, dict)}
        self._history = [copy.deepcopy(self.notes)]
        self._history_index = 0
        self.sort_column = "model"
        self.sort_reverse = False
        self.group_sort_column = "group"
        self.group_sort_reverse = False
        self._group_paths: Dict[str, Tuple[str, ...]] = {}     # tree item -> path of group names
        self.highlight: Dict[str, str] = {}      # groups of the selected model(s): name -> direct/indirect
        self.selected_groups: List[str] = []
        self.shown: List[Dict[str, Any]] = []
        self.kinds: Dict[str, str] = {}
        self._editor = None
        self._group_iids: Dict[str, str] = {}      # tree item -> group name
        self._build()
        self.refresh_models()

    # ------------------------------------------------------------------ building
    def _build(self):
        for attr in ("_plugin_toolbars", "_waveform_toolbars"):
            for w in getattr(self.canvas, attr, None) or []:
                try:
                    w.destroy()
                except tk.TclError:
                    pass
        self._style()
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
        col_box.bind("<<ComboboxSelected>>", lambda e: self.refresh_models())
        self.filter_text = tk.StringVar(value="")
        entry = tk.Entry(bar, textvariable=self.filter_text, width=24, bg=FIELD_BG, fg=FG, insertbackground=FG,
                         selectbackground=SEL_BG, selectforeground=SEL_FG, relief="solid", bd=1)
        entry.pack(side="left", padx=2)
        entry.bind("<KeyRelease>", lambda e: self.refresh_models())
        entry.bind("<Escape>", lambda e: self.clear_filter())
        self.filter_entry = entry
        tk.Button(bar, text="\u2715", command=self.clear_filter, bg="#e2e2e2", fg=FG, activebackground="#cfe0ff",
                  activeforeground=FG, relief="flat", padx=4, pady=0, cursor="hand2").pack(side="left", padx=(0, 10))
        self.clear_groups_btn = tk.Button(bar, text="Clear group selection", command=self.clear_groups,
                                          bg="#e2e2e2", fg=FG, activebackground="#cfe0ff", activeforeground=FG,
                                          relief="flat", padx=6, pady=0, cursor="hand2")
        self.clear_groups_btn.pack(side="left")
        self.count_var = tk.StringVar(value="")
        tk.Label(bar, textvariable=self.count_var, bg=BG, fg=FG).pack(side="left", padx=(10, 0))
        tk.Label(bar, text="gray italic = via a nested group", bg=BG, fg=FG_DIM,
                 font=("TkDefaultFont", 9, "italic")).pack(side="right")
        tk.Label(bar, text=" selected model's groups ", bg=HL_DIRECT_BG, fg=FG).pack(side="right", padx=(0, 8))

        paned = tk.PanedWindow(root, orient="horizontal", sashwidth=6, sashrelief="raised", bg=SASH_BG,
                               bd=0, showhandle=False, opaqueresize=True)
        paned.pack(side="top", fill="both", expand=True)
        self.paned = paned

        left = tk.Frame(paned, bg=BG)
        self.group_tree = ttk.Treeview(left, style="XLayout.Treeview", columns=GROUP_COLUMNS[1:],
                                       selectmode="extended")
        self.group_tree.heading("#0", text=GROUP_HEADINGS["group"], command=lambda: self.sort_groups("group"))
        self.group_tree.column("#0", width=190, stretch=True)
        for col, width in (("count", 60), ("preview", 80), ("master", 52)):
            self.group_tree.heading(col, text=GROUP_HEADINGS[col], command=lambda c=col: self.sort_groups(c))
            self.group_tree.column(col, width=width, anchor="e" if col == "count" else
                                   ("center" if col == "master" else "w"), stretch=False)
        self.group_tree.bind("<<TreeviewOpen>>", lambda e: self._after_idle(self._restripe_groups), add="+")
        self.group_tree.bind("<<TreeviewClose>>", lambda e: self._after_idle(self._restripe_groups), add="+")
        gsb = ttk.Scrollbar(left, orient="vertical", command=self.group_tree.yview)
        self.group_tree.configure(yscrollcommand=gsb.set)
        self._gsb = gsb
        gsb.pack(side="right", fill="y")
        self.group_tree.pack(side="left", fill="both", expand=True)
        self.group_tree.bind("<<TreeviewSelect>>", self._on_group_select)
        self.group_tree.bind("<Escape>", lambda e: self.clear_groups())

        right = tk.Frame(paned, bg=BG)
        self.model_tree = ttk.Treeview(right, style="XLayout.Treeview", columns=COLUMNS, show="headings",
                                       selectmode="extended")
        widths = {"model": 190, "type": 100, "nodes": 64, "preview": 90, "master": 52, "style": 110, "comment": 240}
        for col in COLUMNS:
            self.model_tree.heading(col, text=HEADINGS[col], command=lambda c=col: self.sort_by(c))
            self.model_tree.column(col, width=widths[col], anchor="e" if col == "nodes" else
                                   ("center" if col == "master" else "w"), stretch=(col == "comment"))
        self.model_tree.tag_configure("indirect", foreground=FG_DIM, font=("TkDefaultFont", 9, "italic"))
        self.model_tree.tag_configure("direct", foreground=FG)
        for tree in (self.group_tree, self.model_tree):
            tree.tag_configure("even", background=ROW_BG)
            tree.tag_configure("odd", background=ROW_ALT_BG)
        self.group_tree.tag_configure("hl_direct", background=HL_DIRECT_BG, foreground=FG)
        self.group_tree.tag_configure("hl_indirect", background=HL_INDIRECT_BG, foreground=FG,
                                      font=("TkDefaultFont", 9, "italic"))
        self.model_tree.bind("<<TreeviewSelect>>", self._on_model_select, add="+")
        msb = ttk.Scrollbar(right, orient="vertical", command=self.model_tree.yview)
        hsb = ttk.Scrollbar(right, orient="horizontal", command=self.model_tree.xview)
        self.model_tree.configure(yscrollcommand=msb.set, xscrollcommand=hsb.set)
        self._msb, self._hsb = msb, hsb
        msb.pack(side="right", fill="y")
        hsb.pack(side="bottom", fill="x")
        self.model_tree.pack(side="left", fill="both", expand=True)
        self.model_tree.bind("<Double-1>", self._on_model_double_click)
        self.model_tree.bind("<Button-3>", self._on_model_right_click)
        self.model_tree.bind("<Escape>", lambda e: self.model_tree.selection_set(()))

        sash = get_preference("xlayout_sash", 260)
        try:
            sash = max(120, int(sash))
        except (TypeError, ValueError):
            sash = 260
        paned.add(left, minsize=120, width=sash)
        paned.add(right, minsize=200)
        paned.bind("<ButtonRelease-1>", self._remember_sash, add="+")
        # faint cell borders (ttk.Treeview has none of its own)
        self.grids = [GridLines(self.group_tree), GridLines(self.model_tree)]
        self.grids[0].hook_scrollbars(yset=self._gsb.set)
        self.grids[1].hook_scrollbars(yset=self._msb.set, xset=self._hsb.set)
        self._fill_group_tree()
        self._update_headings()

    def _style(self):
        try:
            style = ttk.Style()
            style.configure("XLayout.Treeview", background=FIELD_BG, fieldbackground=FIELD_BG, foreground=FG,
                            rowheight=20)
            style.map("XLayout.Treeview", background=[("selected", SEL_BG)], foreground=[("selected", SEL_FG)])
            style.configure("XLayout.Treeview.Heading", foreground=FG)
        except (tk.TclError, AttributeError):
            pass

    def case_sensitive(self):
        return bool(get_preference(PREF_SORT_CASE, True))

    def _fill_group_tree(self):
        """(Re)build the group tree in the current group sort order,
        keeping which groups were expanded and selected."""
        tree, groups = self.group_tree, self.layout["groups"]
        opened = {path for iid, path in self._group_paths.items() if self._is_open(iid)}
        selected = {self._group_paths.get(iid) for iid in tree.selection()} if self._group_paths else set()
        tree.delete(*tree.get_children())
        self._group_iids, self._group_paths = {}, {}
        order = lambda names: sort_group_names(self.layout, names, self.group_sort_column,
                                               self.group_sort_reverse, self.case_sensitive())
        reselect = []

        def add(parent, name, path):
            iid = f"g{len(self._group_iids)}"
            self._group_iids[iid], self._group_paths[iid] = name, path
            row = group_row(self.layout, name)
            tree.insert(parent, "end", iid=iid, text=name, open=path in opened,
                        values=(row["count"], row["preview"], master_text(row["master"])))
            if path in selected:
                reselect.append(iid)
            kids = [c for c in groups[name]["groups"] if c not in path and c in groups]
            for child in order(kids):
                add(iid, child, path + (child,))
        for name in order(top_level_groups(self.layout)):
            add("", name, (name,))
        loose = ungrouped_models(self.layout)
        if loose:                        # always last, whatever the sort
            iid = "ungrouped"
            self._group_iids[iid], self._group_paths[iid] = UNGROUPED, (UNGROUPED,)
            tree.insert("", "end", iid=iid, text=UNGROUPED, values=(len(loose), "", ""))
            if (UNGROUPED,) in selected:
                reselect.append(iid)
        if reselect:
            tree.selection_set(reselect)
        self._restripe_groups()

    def _is_open(self, iid):
        try:
            return bool(self.group_tree.item(iid, "open"))
        except (tk.TclError, KeyError):
            return False

    def _restripe_groups(self):
        """Alternate row colors over the rows actually shown (expanded)."""
        tree, n = self.group_tree, 0

        def walk(parent, visible):
            nonlocal n
            for iid in tree.get_children(parent):
                hl = self.highlight.get(self._group_iids.get(iid))
                # a highlighted row gets only the highlight tag (no competing
                # stripe); rows inside collapsed groups are restriped on open
                tree.item(iid, tags=(f"hl_{hl}",) if hl else ("even" if n % 2 == 0 else "odd",))
                if visible:
                    n += 1
                walk(iid, visible and self._is_open(iid))
        try:
            walk("", True)
        except tk.TclError:
            pass
        self._redraw_grids()

    def _on_model_select(self, event=None):
        self.highlight_groups_of(list(self.model_tree.selection()))

    def highlight_groups_of(self, models):
        """Highlight the groups the given models are in (direct: stronger,
        through nested groups: lighter italic), open the tree down to them
        and scroll the first one into view. [] clears the highlight."""
        self.highlight = groups_containing(self.layout, models) if models else {}
        first = None
        if self.highlight:
            for iid, name in self._group_iids.items():       # in tree order
                if name not in self.highlight:
                    continue
                parent = self.group_tree.parent(iid) if hasattr(self.group_tree, "parent") else ""
                while parent:
                    self.group_tree.item(parent, open=True)
                    parent = self.group_tree.parent(parent)
                first = first or iid
        self._restripe_groups()
        if first is not None:
            try:
                self.group_tree.see(first)
            except tk.TclError:
                pass

    def sort_groups(self, column):
        if column == self.group_sort_column:
            self.group_sort_reverse = not self.group_sort_reverse
        else:
            self.group_sort_column, self.group_sort_reverse = column, False
        self._update_headings()
        self._fill_group_tree()

    def refresh_all(self):
        """Re-sort everything (e.g. the case-sensitivity preference changed)."""
        self._fill_group_tree()
        self.refresh_models()

    def _after_idle(self, fn):
        try:
            self.canvas.after_idle(fn)
        except (tk.TclError, AttributeError):
            fn()

    def _redraw_grids(self):
        for grid in getattr(self, "grids", []):
            grid.schedule()

    def _remember_sash(self, event=None):
        try:
            x = int(self.paned.sash_coord(0)[0])
        except (tk.TclError, TypeError, ValueError, IndexError):
            return
        if x > 0:
            set_preference("xlayout_sash", x)

    # ------------------------------------------------------------------ sizes / text panel
    def min_panel_height(self):
        return 160

    def preferred_panel_height(self):
        return 420

    def show_summary(self):
        if self.text is None:
            return
        try:
            self.text.configure(state="normal")
            self.text.delete("1.0", "end")
            insert_styled_text(self.text, layout_summary(self.path, self.layout, self.notes))
            self.text.edit_modified(False)
        except tk.TclError:
            pass

    # ------------------------------------------------------------------ model list
    def rows(self):
        return model_rows(self.layout, self.notes)

    def _filter_key(self):
        label = self.filter_column.get()
        return next((c for c in COLUMNS if HEADINGS[c] == label), ANY_COLUMN)

    def refresh_models(self):
        rows = self.rows()
        self.kinds = groups_to_models(self.layout, self.selected_groups) if self.selected_groups else {}
        if self.selected_groups:
            rows = [r for r in rows if r["model"] in self.kinds]
        rows = filter_rows(rows, self._filter_key(), self.filter_text.get())
        rows = sort_rows(rows, self.sort_column, self.sort_reverse, self.case_sensitive())
        self.shown = rows
        tree = self.model_tree
        keep = set(tree.selection()) if hasattr(tree, "selection") else set()
        tree.delete(*tree.get_children())
        for i, r in enumerate(rows):
            kind = self.kinds.get(r["model"], "direct")
            nodes = nodes_text(r["nodes"], r["type"])
            tree.insert("", "end", iid=r["model"], tags=(kind, "even" if i % 2 == 0 else "odd"),
                        values=(r["model"], r["type"], nodes, r["preview"], master_text(r["master"]),
                                r["style"], r["comment"]))
        still = [iid for iid in keep if iid in {r["model"] for r in rows}]
        if still:
            tree.selection_set(still)
        total = len(self.layout["models"])
        indirect = sum(1 for r in rows if self.kinds.get(r["model"]) == "indirect")
        text = f"{len(rows)} of {total} models"
        if indirect:
            text += f"  ({indirect} via nested groups)"
        self.count_var.set(text)
        self._redraw_grids()

    def _update_headings(self):
        for col in COLUMNS:
            arrow = ""
            if col == self.sort_column:
                arrow = " \u25bc" if self.sort_reverse else " \u25b2"
            self.model_tree.heading(col, text=HEADINGS[col] + arrow)
        for col in GROUP_COLUMNS:
            arrow = ""
            if col == self.group_sort_column:
                arrow = " \u25bc" if self.group_sort_reverse else " \u25b2"
            self.group_tree.heading("#0" if col == "group" else col, text=GROUP_HEADINGS[col] + arrow)

    def sort_by(self, column):
        if column == self.sort_column:
            self.sort_reverse = not self.sort_reverse
        else:
            self.sort_column, self.sort_reverse = column, False
        self._update_headings()
        self.refresh_models()

    def set_filter(self, column, spec):
        self.filter_column.set(HEADINGS.get(column, ANY_COLUMN))
        self.filter_text.set(spec)
        self.refresh_models()

    def clear_filter(self):
        self.filter_text.set("")
        self.refresh_models()

    # ------------------------------------------------------------------ groups
    def _on_group_select(self, event=None):
        names = []
        for iid in self.group_tree.selection():
            name = self._group_iids.get(iid)
            if name and name not in names:
                names.append(name)
        self.select_groups(names, from_tree=True)

    def select_groups(self, names, from_tree=False):
        self.selected_groups = [n for n in names if n in self.layout["groups"] or n == UNGROUPED]
        if not from_tree:
            iids = [iid for iid, n in self._group_iids.items() if n in self.selected_groups]
            try:
                self.group_tree.selection_set(iids)
            except tk.TclError:
                pass
        self.refresh_models()

    def clear_groups(self):
        try:
            self.group_tree.selection_set(())
        except tk.TclError:
            pass
        self.select_groups([])

    # ------------------------------------------------------------------ notes (style / comment)
    def styles_in_use(self):
        styles = {n.get("style") for n in self.notes.values() if n.get("style")}
        styles |= set(get_preference("xlayout_styles", []) or [])
        return sorted(styles, key=lambda v: natural_key(v, self.case_sensitive()))

    def set_note(self, models, column, value):
        """Set Style or Comment for these models: one undo step, marks the
        tab unsaved. Returns True if anything changed."""
        if column not in EDITABLE:
            return False
        value = (value or "").strip()
        changed = False
        for name in models:
            if name not in self.layout["models"]:
                continue
            note = self.notes.setdefault(name, {})
            if note.get(column, "") != value:
                if value:
                    note[column] = value
                else:
                    note.pop(column, None)
                changed = True
            if not note:
                self.notes.pop(name, None)
        if not changed:
            return False
        if column == "style" and value:
            known = list(get_preference("xlayout_styles", []) or [])
            if value not in known:
                set_preference("xlayout_styles", known + [value])
        self._push_history()
        self._changed()
        return True

    def _changed(self):
        mark_dirty = getattr(self.tab, "mark_dirty", None) if self.tab is not None else None
        if callable(mark_dirty):
            mark_dirty()
        else:
            self.save()
        self.refresh_models()
        self.show_summary()          # its "with a style or comment" count

    def save(self):
        """tab.save_hook: write the notes to the sidecar (never the layout)."""
        return th.update_cache(self.path, **{NOTES_KEY: self.notes})

    def _push_history(self):
        del self._history[self._history_index + 1:]
        self._history.append(copy.deepcopy(self.notes))
        if len(self._history) > UNDO_LIMIT + 1:
            del self._history[:len(self._history) - UNDO_LIMIT - 1]
        self._history_index = len(self._history) - 1

    def undo(self):
        if self._history_index > 0:
            self._history_index -= 1
            self.notes = copy.deepcopy(self._history[self._history_index])
            self._changed()

    def redo(self):
        if self._history_index < len(self._history) - 1:
            self._history_index += 1
            self.notes = copy.deepcopy(self._history[self._history_index])
            self._changed()

    # ------------------------------------------------------------------ in-place editing
    def _column_at(self, x):
        try:
            col = self.model_tree.identify_column(x)      # "#1".."#5"
            return COLUMNS[int(str(col).lstrip("#")) - 1]
        except (tk.TclError, ValueError, IndexError, TypeError):
            return None

    def _on_model_double_click(self, event):
        iid = self.model_tree.identify_row(event.y)
        column = self._column_at(event.x)
        if iid and column in EDITABLE:
            self.begin_edit(iid, column)
            return "break"
        return None

    def begin_edit(self, model, column):
        """An editor over the cell: a combobox of known styles for Style,
        a plain entry for Comment. Enter / leaving it saves, Esc cancels."""
        self.end_edit(commit=False)
        try:
            bbox = self.model_tree.bbox(model, column)
        except tk.TclError:
            bbox = None
        current = (self.notes.get(model) or {}).get(column, "")
        var = tk.StringVar(value=current)
        if column == "style":
            editor = ttk.Combobox(self.model_tree, textvariable=var, values=self.styles_in_use())
            editor.bind("<<ComboboxSelected>>", lambda e: self.end_edit(commit=True))
        else:
            editor = tk.Entry(self.model_tree, textvariable=var, bg=FIELD_BG, fg=FG, insertbackground=FG,
                              selectbackground=SEL_BG, selectforeground=SEL_FG, relief="solid", bd=1)
        self._editor = {"widget": editor, "var": var, "model": model, "column": column}
        if bbox:
            x, y, w, h = bbox
            editor.place(x=x, y=y, width=w, height=h)
        editor.bind("<Return>", lambda e: self.end_edit(commit=True))
        editor.bind("<KP_Enter>", lambda e: self.end_edit(commit=True))
        editor.bind("<Escape>", lambda e: self.end_edit(commit=False))
        editor.bind("<FocusOut>", lambda e: self._maybe_commit_later())
        try:
            editor.focus_set()
            editor.select_range(0, "end")
        except tk.TclError:
            pass
        return editor

    def _maybe_commit_later(self):
        """FocusOut: commit, unless the focus only went to the combobox's
        own drop-down list."""
        def check():
            ed = self._editor
            if ed is None:
                return
            try:
                focus = str(self.model_tree.focus_get() or "")
            except (tk.TclError, KeyError):
                focus = ""
            if focus.startswith(str(ed["widget"])) or "popdown" in focus:
                return
            self.end_edit(commit=True)
        try:
            self.model_tree.after(120, check)
        except tk.TclError:
            check()

    def end_edit(self, commit=True):
        ed, self._editor = self._editor, None
        if ed is None:
            return "break"
        value = ed["var"].get()
        try:
            ed["widget"].destroy()
        except tk.TclError:
            pass
        if commit:
            self.set_note([ed["model"]], ed["column"], value)
        try:
            self.model_tree.focus_set()
        except tk.TclError:
            pass
        return "break"

    # ------------------------------------------------------------------ right-click
    def _on_model_right_click(self, event):
        iid = self.model_tree.identify_row(event.y)
        column = self._column_at(event.x)
        if iid and iid not in self.model_tree.selection():
            self.model_tree.selection_set((iid,))
        menu = self.build_model_menu(iid, column)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                menu.grab_release()
            except tk.TclError:
                pass
        return "break"

    def build_model_menu(self, iid, column):
        selected = [s for s in self.model_tree.selection()] or ([iid] if iid else [])
        n = len(selected)
        what = f"{n} selected model{'s' if n != 1 else ''}"
        menu = tk.Menu(self.model_tree, tearoff=False, bg=FIELD_BG, fg=FG, activebackground="#cfe0ff",
                       activeforeground=FG, disabledforeground=FG_DIM)
        state = "normal" if n else "disabled"
        styles = tk.Menu(menu, tearoff=False, bg=FIELD_BG, fg=FG, activebackground="#cfe0ff", activeforeground=FG)
        for st in self.styles_in_use():
            styles.add_command(label=st, command=lambda v=st: self.set_note(selected, "style", v))
        if self.styles_in_use():
            styles.add_separator()
        styles.add_command(label="New style...", command=lambda: self.ask_note(selected, "style"))
        menu.add_cascade(label=f"Set style for {what}", menu=styles, state=state)
        menu.add_command(label=f"Set comment for {what}...", state=state,
                         command=lambda: self.ask_note(selected, "comment"))
        menu.add_command(label=f"Clear style of {what}", state=state,
                         command=lambda: self.set_note(selected, "style", ""))
        menu.add_command(label=f"Clear comment of {what}", state=state,
                         command=lambda: self.set_note(selected, "comment", ""))
        if iid and column:
            row = next((r for r in self.rows() if r["model"] == iid), None)
            raw = None if row is None else row[column]
            value = master_text(raw) if column == "master" else ("" if raw is None else str(raw))
            menu.add_separator()
            shown = value if len(value) <= 30 else value[:29] + "\u2026"
            menu.add_command(label=f"Filter: {HEADINGS[column]} = \u201c{shown}\u201d",
                             command=lambda: self.set_filter(column, "=" + value))
            menu.add_command(label=f"Filter: {HEADINGS[column]} \u2260 \u201c{shown}\u201d",
                             command=lambda: self.set_filter(column, "!=" + value))
        if self.filter_text.get().strip():
            menu.add_command(label="Clear the filter", command=self.clear_filter)
        self._last_menu = menu
        return menu

    def ask_note(self, models, column):
        if not models:
            return False
        first = (self.notes.get(models[0]) or {}).get(column, "")
        try:
            value = simpledialog.askstring(HEADINGS[column], f"{HEADINGS[column]} for {len(models)} model"
                                           f"{'s' if len(models) != 1 else ''}:", initialvalue=first,
                                           parent=self.canvas.winfo_toplevel())
        except tk.TclError:
            value = None
        if value is None:
            return False
        return self.set_note(models, column, value)


# eof
