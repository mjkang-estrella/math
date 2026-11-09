"""Structured, read-only git queries with timeouts and output caps.

Only fixed subcommands are run, arguments are passed as a list (no shell), and
GIT_OPTIONAL_LOCKS=0 keeps `git status` from writing the index while research
agents are working. Failures are returned as values, never raised.
"""

from __future__ import annotations

import os
import re
import subprocess
from dataclasses import dataclass, field

GIT_TIMEOUT = 5.0
MAX_OUTPUT = 4 * 1024 * 1024
HASH_RE = re.compile(r"[0-9a-f]{7,40}")
FINDING_ID_RE = re.compile(r"(?<![A-Za-z0-9])[Ww](\d{2,4})(?![0-9])")  # in file names; normalized to W###

_REC, _FLD = "\x1e", "\x1f"


@dataclass
class GitResult:
    ok: bool
    out: str = ""
    error: str = ""


@dataclass
class Commit:
    hash: str
    short: str
    author_date: str
    commit_date: str
    author: str
    subject: str
    body: str
    files: list[str] = field(default_factory=list)
    finding_ids: list[str] = field(default_factory=list)

    def to_json(self) -> dict:
        return {
            "hash": self.hash,
            "short": self.short,
            "author_date": self.author_date,
            "commit_date": self.commit_date,
            "author": self.author,
            "subject": self.subject,
            "body": self.body,
            "files": self.files[:80],
            "file_count": len(self.files),
            "finding_ids": self.finding_ids,
        }


def run_git(repo: str, args: list[str], timeout: float = GIT_TIMEOUT) -> GitResult:
    env = {
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "HOME": os.environ.get("HOME", "/tmp"),
        "LC_ALL": "C",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_TERMINAL_PROMPT": "0",
        "GIT_PAGER": "cat",
    }
    try:
        proc = subprocess.run(
            ["git", "-C", repo, "--no-pager", *args],
            capture_output=True,
            timeout=timeout,
            env=env,
            stdin=subprocess.DEVNULL,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return GitResult(False, error=f"git {args[0]} timed out after {timeout:.0f}s")
    except OSError as exc:
        return GitResult(False, error=f"git unavailable: {exc.strerror}")
    out = proc.stdout[:MAX_OUTPUT].decode("utf-8", errors="replace")
    if proc.returncode != 0:
        err = proc.stderr[:2000].decode("utf-8", errors="replace").strip()
        return GitResult(False, out, err or f"git {args[0]} exited {proc.returncode}")
    return GitResult(True, out)


def head(repo: str) -> dict:
    res = run_git(repo, ["rev-parse", "HEAD"])
    branch = run_git(repo, ["symbolic-ref", "--short", "-q", "HEAD"])
    return {
        "ok": res.ok,
        "hash": res.out.strip() if res.ok else None,
        "branch": branch.out.strip() if branch.ok and branch.out.strip() else None,
        "error": None if res.ok else res.error,
    }


def log(repo: str, limit: int = 200, pathspec: str | None = None) -> tuple[list[Commit], str | None]:
    fmt = _REC + _FLD.join(["%H", "%h", "%aI", "%cI", "%an", "%s", "%b"]) + _FLD
    args = ["log", f"-n{int(limit)}", f"--format={fmt}", "--name-only", "--no-color", "--no-renames"]
    if pathspec:
        args += ["--", pathspec]
    res = run_git(repo, args)
    if not res.ok:
        return [], res.error
    return parse_log(res.out), None


def parse_log(text: str) -> list[Commit]:
    commits: list[Commit] = []
    for record in text.split(_REC):
        if not record.strip():
            continue
        parts = record.split(_FLD)
        if len(parts) < 8:
            continue
        h, short, adate, cdate, author, subject, body = parts[:7]
        if not HASH_RE.fullmatch(h):
            continue
        files = [ln.strip() for ln in parts[7].splitlines() if ln.strip()]
        ids = sorted({"W%03d" % int(m) for f in files for m in FINDING_ID_RE.findall(os.path.basename(f))})
        commits.append(Commit(h, short, adate, cdate, author, subject.strip(), body.strip(), files, ids))
    return commits


def status(repo: str, pathspec: str | None = None) -> tuple[list[dict], str | None]:
    args = ["status", "--porcelain=v1", "-z", "--untracked-files=all", "--no-renames"]
    if pathspec:
        args += ["--", pathspec]
    res = run_git(repo, args)
    if not res.ok:
        return [], res.error
    return parse_status(res.out), None


_STATUS_LABEL = {"?": "untracked", "M": "modified", "A": "added", "D": "deleted", "R": "renamed", "U": "conflict", "T": "type change"}


def parse_status(text: str) -> list[dict]:
    entries = []
    for item in text.split("\x00"):
        if len(item) < 4 or item[2] != " ":
            continue
        code, path = item[:2], item[3:]
        key = "?" if code == "??" else (code[0] if code[0] != " " else code[1])
        entries.append({"code": code, "state": _STATUS_LABEL.get(key, "changed"), "path": path})
    return entries


def show_commit(repo: str, ref: str) -> dict:
    if not isinstance(ref, str) or not HASH_RE.fullmatch(ref):
        return {"ok": False, "error": "commit must be a 7-40 character lowercase hex hash"}
    exists = run_git(repo, ["cat-file", "-e", f"{ref}^{{commit}}"])
    if not exists.ok:
        return {"ok": False, "error": "unknown commit"}
    fmt = _FLD.join(["%H", "%h", "%aI", "%cI", "%an", "%s", "%b"]) + _REC
    res = run_git(repo, ["show", "--no-color", "--stat=120", "--no-renames", f"--format={fmt}", ref, "--"])
    if not res.ok:
        return {"ok": False, "error": res.error}
    head_part, _, stat_part = res.out.partition(_REC)
    parts = head_part.split(_FLD)
    if len(parts) < 7:
        return {"ok": False, "error": "unexpected git output"}
    return {
        "ok": True,
        "hash": parts[0], "short": parts[1], "author_date": parts[2], "commit_date": parts[3],
        "author": parts[4], "subject": parts[5], "body": parts[6].strip(),
        "stat": stat_part.strip()[:200_000],
    }
