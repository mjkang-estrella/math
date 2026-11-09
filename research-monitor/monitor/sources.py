"""Allowlisted, read-only access to research text files.

Only a fixed set of relative path shapes inside the research directory can be
listed or read. Paths are validated syntactically first (no `..`, no absolute
paths, no hidden names), then resolved and required to be regular files whose
real path equals the expected location, so symlinks cannot escape the tree.
"""

from __future__ import annotations

import os
import re
import stat
from dataclasses import dataclass

MAX_SOURCE_BYTES = 2 * 1024 * 1024
_NAME = r"[A-Za-z0-9][A-Za-z0-9._-]{0,120}"

# (directory relative to research root, filename regex). Directory "" is root.
ALLOWED_LOCATIONS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("", re.compile(r"(README\.md|RESEARCH_LOOP\.md|RESEARCH_TEAM\.md|Audit\.lean|Research\.lean|Main\.lean|lakefile\.toml|lean-toolchain)")),
    ("research", re.compile(r"STATE\.md")),
    ("research/findings", re.compile(_NAME + r"\.(md|json|txt)")),
    ("research/proposals", re.compile(_NAME + r"\.md")),
    ("research/proposals/archive", re.compile(_NAME + r"\.md")),
    ("research/artifacts", re.compile(_NAME + r"\.(md|json|txt|py)")),
    ("Research", re.compile(_NAME + r"\.lean")),
    ("scripts", re.compile(_NAME + r"\.(py|sh|lean)")),
)


class SourceError(Exception):
    """Raised for rejected or unreadable source requests (message is safe to show)."""

    def __init__(self, message: str, status: int = 404):
        super().__init__(message)
        self.status = status


@dataclass
class SourceFile:
    path: str
    text: str
    size: int
    mtime: float
    truncated: bool


def is_allowed(rel: str) -> bool:
    if not isinstance(rel, str) or not rel or len(rel) > 300:
        return False
    if rel.startswith("/") or "\\" in rel or "\x00" in rel:
        return False
    parts = rel.split("/")
    if any(p in ("", ".", "..") or p.startswith(".") for p in parts):
        return False
    directory, name = "/".join(parts[:-1]), parts[-1]
    if ".." in name:
        return False
    return any(directory == d and pat.fullmatch(name) for d, pat in ALLOWED_LOCATIONS)


def _resolve(root: str, rel: str) -> str:
    if not is_allowed(rel):
        raise SourceError("path is not an allowlisted research source", 403)
    root_real = os.path.realpath(root)
    candidate = os.path.join(root_real, *rel.split("/"))
    if os.path.realpath(candidate) != candidate:
        raise SourceError("path resolves outside its expected location", 403)
    return candidate


def stat_source(root: str, rel: str) -> os.stat_result | None:
    try:
        full = _resolve(root, rel)
        st = os.stat(full, follow_symlinks=False)
    except (SourceError, OSError):
        return None
    return st if stat.S_ISREG(st.st_mode) else None


def read_source(root: str, rel: str, max_bytes: int = MAX_SOURCE_BYTES) -> SourceFile:
    full = _resolve(root, rel)
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(full, flags)
    except FileNotFoundError:
        raise SourceError("source not found", 404) from None
    except OSError:
        raise SourceError("source could not be opened", 404) from None
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise SourceError("source is not a regular file", 403)
        with os.fdopen(fd, "rb", closefd=False) as fh:
            data = fh.read(max_bytes + 1)
    finally:
        os.close(fd)
    truncated = len(data) > max_bytes
    data = data[:max_bytes]
    return SourceFile(rel, data.decode("utf-8", errors="replace"), st.st_size, st.st_mtime, truncated)


def try_read(root: str, rel: str, max_bytes: int = MAX_SOURCE_BYTES) -> SourceFile | None:
    try:
        return read_source(root, rel, max_bytes)
    except (SourceError, OSError):
        return None


def list_sources(root: str) -> list[str]:
    """All allowlisted files that currently exist, sorted."""
    out: list[str] = []
    root_real = os.path.realpath(root)
    for directory, _ in ALLOWED_LOCATIONS:
        full_dir = os.path.join(root_real, *directory.split("/")) if directory else root_real
        try:
            names = os.listdir(full_dir)
        except OSError:
            continue
        for name in names:
            rel = f"{directory}/{name}" if directory else name
            if is_allowed(rel) and stat_source(root, rel) is not None:
                out.append(rel)
    return sorted(set(out))
