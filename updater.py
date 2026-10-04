"""Help > Check for Updates: compare this copy's VERSION (tracked.py)
with the one in the GitHub repository, and update the program files from
the repository's zip if it's newer.

  repo      "owner/name" (Preferences > Updates from GitHub repository)
  branch    "main" by default

Updating: every file in the zip that differs from the local copy is
written; the local version is first copied to
~/.tracked/update-backup-<time>/ (so an update can be undone by copying
those back). Local files the zip doesn't have are left alone. Python
files changed -> trackED needs a restart.

Network access is plain HTTPS to github.com / raw.githubusercontent.com
(urllib, no extra packages). No Tk here.
"""

from __future__ import annotations

import io
import os
import re
import shutil
import time
import urllib.request
import zipfile
from pathlib import Path
from typing import List, Optional, Tuple

# The repository updates come from when the user hasn't set one in
# Preferences: fill in "owner/name" for the official copy. (A git clone
# of the project finds its own repository automatically -- see
# default_repo -- so this is only for copies installed from a zip.)
UPDATE_REPO = "djulien/trackED"
UPDATE_BRANCH = "main"

TIMEOUT = 20
VERSION_RE = re.compile(r'^VERSION\s*=\s*["\']([^"\']+)["\']', re.M)
SKIP_PARTS = {".git", ".github", "__pycache__"}


def parse_version(text: str) -> Tuple[int, ...]:
    """"1.2.10" -> (1, 2, 10); anything after the numbers is ignored."""
    nums = re.findall(r"\d+", (text or "").split("-")[0].split("+")[0])
    return tuple(int(n) for n in nums) or (0,)


def is_newer(remote: str, local: str) -> bool:
    a, b = parse_version(remote), parse_version(local)
    n = max(len(a), len(b))
    return a + (0,) * (n - len(a)) > b + (0,) * (n - len(b))


def valid_repo(repo: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", (repo or "").strip()))


def repo_from_git(app_dir: str) -> str:
    """"owner/name" of the GitHub remote "origin" when app_dir is a git
    clone (read from .git/config; no git program needed), else ""."""
    try:
        text = (Path(app_dir) / ".git" / "config").read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""
    m = re.search(r'\[remote "origin"\][^\[]*?url\s*=\s*(\S+)', text, re.S)
    if not m:
        return ""
    m2 = re.search(r"github\.com[:/]([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+?)(?:\.git)?/?$", m.group(1))
    return m2.group(1) if m2 else ""


def default_repo(preference: str, app_dir: str) -> str:
    """Where updates come from: the Preferences setting, else this copy's
    own git remote, else UPDATE_REPO."""
    for repo in ((preference or "").strip(), repo_from_git(app_dir), UPDATE_REPO):
        if valid_repo(repo):
            return repo
    return ""


def _get(url: str) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": "trackED-updater"})
    with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
        return resp.read()


def remote_version(repo: str, branch: str = "main", fetch=_get) -> str:
    """The VERSION in the repository's tracked.py."""
    text = fetch(f"https://raw.githubusercontent.com/{repo}/{branch}/tracked.py").decode("utf-8", "replace")
    m = VERSION_RE.search(text)
    if not m:
        raise RuntimeError("no VERSION line in the repository's tracked.py")
    return m.group(1)


def download(repo: str, branch: str = "main", fetch=_get) -> bytes:
    return fetch(f"https://github.com/{repo}/archive/refs/heads/{branch}.zip")


def apply_zip(data: bytes, app_dir: str, backup_root: Optional[str] = None) -> Tuple[List[str], Optional[str]]:
    """Write the zip's files over app_dir where they differ. Returns
    (changed relative paths, backup folder or None)."""
    app = Path(app_dir)
    backup = Path(backup_root or Path.home() / ".tracked") / f"update-backup-{time.strftime('%Y%m%d-%H%M%S')}"
    changed: List[str] = []
    with zipfile.ZipFile(io.BytesIO(data)) as zf:
        names = [n for n in zf.namelist() if not n.endswith("/")]
        top = os.path.commonprefix([n.split("/", 1)[0] + "/" for n in names]) if names else ""
        for name in names:
            rel = name[len(top):] if top and name.startswith(top) else name
            parts = Path(rel).parts
            if not rel or any(p in SKIP_PARTS for p in parts) or ".." in parts or Path(rel).is_absolute():
                continue
            new = zf.read(name)
            dest = app / rel
            if dest.exists() and dest.read_bytes() == new:
                continue
            if dest.exists():
                (backup / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(dest, backup / rel)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(new)
            changed.append(rel.replace("\\", "/"))
    return changed, (str(backup) if backup.exists() else None)


def needs_restart(changed: List[str]) -> bool:
    return any(p.endswith(".py") for p in changed)
