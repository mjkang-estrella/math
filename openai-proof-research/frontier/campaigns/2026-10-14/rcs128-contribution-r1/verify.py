#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only, external-anchor identity verification for the RCS128 contribution
review packet. Establishes byte identity and replays finite diagnostics only;
it carries no mathematical, contribution or priority verdict."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import re
import subprocess
import sys

AUTHOR = {
    "MANIFEST.json": "a81ea2335db99c097423af9baf5abd272fa556ab6f08d870b8d184ee23bb96a6",
    "candidate.md": "ebfed67a43a306af4788c39300e2a418f82193c826bae130508fd87955d39137",
    "original-scope.txt": "7dfa38dbfdc0298863bbd29c76af27061d9f033cf67aa0800979e3310de1eb60",
    "checkpoint.md": "3ab70804621cccba5319e45b18f21b267b3ac8d3cf15deb1aa59f8d415085bf0",
    "contribution-and-limits.md": "55bc1c355f3b33fc54f329d8ebf044d6f6e0b45c4a2d4b15c0397f5070ab7eab",
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(value):
    require(isinstance(value, str) and value, "bad path")
    p = PurePosixPath(value)
    require(not p.is_absolute() and ".." not in p.parts and str(p) == value, "unsafe path")
    return value


def check(root, anchor):
    require(re.fullmatch(r"[0-9a-f]{64}", anchor) is not None, "invalid external anchor")
    mpath = root / "manifest.json"
    require(not root.is_symlink() and not mpath.is_symlink(), "symlink root or manifest")
    raw = mpath.read_bytes()
    require(sha(raw) == anchor, "external anchor mismatch")
    obj = json.loads(raw)
    rows = obj["files"]
    listed = [safe(r["path"]) for r in rows]
    dirs = [safe(d) for d in obj["directories"]]
    require(len(listed) == len(set(listed)), "duplicate file")
    require("manifest.json" not in listed, "manifest listed as payload")
    files, found_dirs = set(), set()
    for p in root.rglob("*"):
        require(not p.is_symlink(), "symlink forbidden")
        rel = p.relative_to(root).as_posix()
        if p.is_file():
            files.add(rel)
        elif p.is_dir():
            found_dirs.add(rel)
        else:
            raise ValueError("nonregular entry")
    require(files == set(listed) | {"manifest.json"}, "file membership mismatch")
    require(found_dirs == set(dirs), "directory membership mismatch")
    for r in rows:
        data = (root / r["path"]).read_bytes()
        require(len(data) == r["bytes"] and sha(data) == r["sha256"], "payload mismatch: " + r["path"])
    return len(rows)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--anchor", required=True, help="manifest SHA256 supplied outside this packet")
    ap.add_argument("--replay", action="store_true")
    ap.add_argument("--author-root", help="optional path to the frozen r37 author packet")
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    n = check(root, args.anchor)
    if args.replay:
        r = subprocess.run([sys.executable, "-I", "-B", str(root / "independent_checks.py"),
                            "--compare", str(root / "independent-checks.json")],
                           capture_output=True, text=True)
        require(r.returncode == 0 and r.stdout.strip() == "MATCH", "diagnostic replay mismatch")
    author = None
    if args.author_root:
        a = Path(args.author_root).resolve()
        for name, h in AUTHOR.items():
            require(sha((a / name).read_bytes()) == h, "author hash mismatch: " + name)
        author = len(AUTHOR)
    print(json.dumps({"status": "PASS", "payload_files": n, "replayed": args.replay,
                      "author_hashes_checked": author,
                      "meaning": "identity and finite diagnostics only; no proof, acceptance or priority"}))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:  # noqa: BLE001
        print("FAIL: " + str(exc), file=sys.stderr)
        sys.exit(1)
