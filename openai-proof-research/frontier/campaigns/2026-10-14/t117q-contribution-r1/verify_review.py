#!/usr/bin/env python3
"""Seal or verify the T117Q contribution review r1 package.

  verify_review.py seal ROOT              write ROOT/MANIFEST.json, print its SHA256
  verify_review.py verify ROOT --anchor H require SHA256(MANIFEST.json) == H

The anchor must come from outside the package. The Git-ignored private/ directory holds
third-party texts and is excluded from membership, but it must be a real directory.
"""
import argparse
import hashlib
import json
import os
import stat
import sys

SCHEMA = "t117q-contribution-r1-review-manifest-v1"
MANIFEST = "MANIFEST.json"
EXCLUDED = ("private",)


class Reject(Exception):
    pass


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def scan(root):
    """Return (files, dirs) relative to root; reject anything but plain nodes."""
    st = os.lstat(root)
    if not stat.S_ISDIR(st.st_mode):
        raise Reject("symlink or nonregular node: .")
    files, dirs = [], []
    stack = [""]
    while stack:
        rel = stack.pop()
        here = os.path.join(root, rel) if rel else root
        for name in sorted(os.listdir(here)):
            r = f"{rel}/{name}" if rel else name
            st = os.lstat(os.path.join(root, r))
            if not rel and name in EXCLUDED:
                if not stat.S_ISDIR(st.st_mode):
                    raise Reject(f"symlink or nonregular node: {r}")
                continue
            if stat.S_ISDIR(st.st_mode):
                dirs.append(r)
                stack.append(r)
            elif stat.S_ISREG(st.st_mode):
                if name == MANIFEST and r != MANIFEST:
                    raise Reject(f"nested manifest: {r}")
                if st.st_nlink != 1:
                    raise Reject(f"hardlinked regular file: {r}")
                files.append(r)
            else:
                raise Reject(f"symlink or nonregular node: {r}")
    return sorted(files), sorted(dirs)


def seal(root):
    files, dirs = scan(root)
    payload = [f for f in files if f != MANIFEST]
    doc = {
        "schema": SCHEMA,
        "excluded_ignored_directories": list(EXCLUDED),
        "directories": dirs,
        "files": [
            {"path": p, "bytes": os.path.getsize(os.path.join(root, p)),
             "sha256": sha256(os.path.join(root, p))}
            for p in payload
        ],
    }
    with open(os.path.join(root, MANIFEST), "w", encoding="utf-8") as f:
        f.write(json.dumps(doc, indent=2, sort_keys=True) + "\n")
    return sha256(os.path.join(root, MANIFEST))


def verify(root, anchor):
    if not anchor or len(anchor) != 64 or any(c not in "0123456789abcdef" for c in anchor):
        raise Reject("external anchor missing or malformed")
    files, dirs = scan(root)
    if MANIFEST not in files:
        raise Reject("manifest missing")
    if sha256(os.path.join(root, MANIFEST)) != anchor:
        raise Reject("external manifest anchor mismatch")
    with open(os.path.join(root, MANIFEST), encoding="utf-8") as f:
        doc = json.load(f)
    if doc.get("schema") != SCHEMA or doc.get("excluded_ignored_directories") != list(EXCLUDED):
        raise Reject("manifest schema mismatch")
    listed = {e["path"]: e for e in doc["files"]}
    if sorted(listed) != [f for f in files if f != MANIFEST]:
        raise Reject("exact file inventory mismatch")
    if sorted(doc["directories"]) != dirs:
        raise Reject("exact directory inventory mismatch")
    for p, e in sorted(listed.items()):
        full = os.path.join(root, p)
        if os.path.getsize(full) != e["bytes"] or sha256(full) != e["sha256"]:
            raise Reject(f"payload mismatch: {p}")
    return len(listed), len(dirs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["seal", "verify"])
    ap.add_argument("root")
    ap.add_argument("--anchor")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    try:
        if a.mode == "seal":
            print(seal(root))
        else:
            n, d = verify(root, a.anchor)
            print(f"PASS ({n} payload files, {d} directories)")
    except Reject as e:
        print(f"FAIL: {e}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
