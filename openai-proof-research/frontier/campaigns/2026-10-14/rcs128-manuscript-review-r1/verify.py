#!/usr/bin/env python3
"""Read-only verifier for the RCS128 manuscript review r1 packet.

Usage: python3 verify.py --anchor <sha256 of MANIFEST.json> [--root DIR]

The anchor must come from the external handoff; it is not stored in the packet.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import stat
import sys

FORMAT = "rcs128-manuscript-review-r1-inventory-v1"


def fail(msg):
    raise ValueError(msg)


def check(root, anchor):
    if not re.fullmatch(r"[0-9a-f]{64}", anchor):
        fail("malformed external anchor")
    root = pathlib.Path(os.path.abspath(root))
    for p in [root, *root.parents]:
        st = os.lstat(p)
        if stat.S_ISLNK(st.st_mode) or not stat.S_ISDIR(st.st_mode):
            fail("root or ancestor not a real directory: " + str(p))
    mpath = root / "MANIFEST.json"
    st = os.lstat(mpath)
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        fail("manifest not a singly linked regular file")
    raw = mpath.read_bytes()
    if hashlib.sha256(raw).hexdigest() != anchor:
        fail("external manifest anchor mismatch")
    m = json.loads(raw)
    if m.get("format") != FORMAT:
        fail("unsupported manifest format")
    files, dirs = m.get("files"), m.get("directories")
    if not isinstance(files, dict) or not isinstance(dirs, list) or len(dirs) != len(set(dirs)):
        fail("invalid manifest structure")
    for name in [*files, *dirs]:
        q = pathlib.PurePosixPath(name)
        if not name or q.is_absolute() or ".." in q.parts or str(q) != name or name == "MANIFEST.json":
            fail("invalid manifest path: " + name)
    actual, seen_dirs = {}, []

    def walk(d):
        with os.scandir(d) as it:
            for e in it:
                p = pathlib.Path(e.path)
                rel = p.relative_to(root).as_posix()
                s = os.lstat(p)
                if stat.S_ISLNK(s.st_mode):
                    fail("symlink: " + rel)
                if stat.S_ISDIR(s.st_mode):
                    seen_dirs.append(rel)
                    walk(p)
                elif stat.S_ISREG(s.st_mode):
                    if s.st_nlink != 1:
                        fail("hardlink: " + rel)
                    if rel != "MANIFEST.json":
                        actual[rel] = {"bytes": s.st_size, "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
                else:
                    fail("nonregular node: " + rel)

    walk(root)
    if set(seen_dirs) != set(dirs):
        fail("directory inventory mismatch")
    if set(actual) != set(files):
        fail("file inventory mismatch")
    for name, rec in files.items():
        if rec != actual[name]:
            fail("file content/size mismatch: " + name)
    return {
        "status": "PASS_INTEGRITY_ONLY",
        "manifest_sha256": anchor,
        "files": len(actual),
        "directories": len(seen_dirs),
        "note": "read-only exact inventory under a caller-supplied external anchor; says nothing about mathematics",
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(pathlib.Path(__file__).absolute().parent))
    ap.add_argument("--anchor", required=True)
    a = ap.parse_args()
    try:
        print(json.dumps(check(a.root, a.anchor), sort_keys=True))
    except Exception as e:  # any failure is a rejection
        print("REJECT: " + str(e), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
