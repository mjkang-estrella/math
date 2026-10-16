#!/usr/bin/env python3
# Myeongjin Kang; no affiliation. MIT License.
# Read-only authentication of the frozen LR-r2 package against an external seal.
# Usage: authenticate_lr_r2.py <package-dir> <expected-seal-sha256> <out-json-or-dash>
import hashlib
import json
import os
import stat
import sys


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def fail(msg):
    sys.stderr.write("AUTH_REJECT: " + msg + "\n")
    sys.exit(1)


def main():
    root, anchor, out = sys.argv[1], sys.argv[2], sys.argv[3]
    root = os.path.realpath(root)
    seal_path = os.path.join(root, "seal.json")
    if os.path.islink(seal_path):
        fail("seal symlink")
    seal_bytes = open(seal_path, "rb").read()
    if hashlib.sha256(seal_bytes).hexdigest() != anchor:
        fail("external seal anchor mismatch")
    seal = json.loads(seal_bytes)
    man_path = os.path.join(root, "manifest.json")
    man_bytes = open(man_path, "rb").read()
    if len(man_bytes) != seal["manifest_size"] or hashlib.sha256(man_bytes).hexdigest() != seal["manifest_sha256"]:
        fail("manifest mismatch")
    man = json.loads(man_bytes)
    seen = set()
    for e in man["files"]:
        p = e["path"]
        if p in seen:
            fail("duplicate path " + p)
        seen.add(p)
        if p.startswith("/") or ".." in p.split("/") or p in man["metadata"]:
            fail("unsafe path " + p)
    actual_files, actual_dirs = set(), set()
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        rel = os.path.relpath(dirpath, root)
        actual_dirs.add("." if rel == "." else rel)
        for n in dirnames + filenames:
            full = os.path.join(dirpath, n)
            st = os.lstat(full)
            if stat.S_ISLNK(st.st_mode):
                fail("symlink " + full)
        for n in filenames:
            r = os.path.relpath(os.path.join(dirpath, n), root)
            actual_files.add(r)
    expected = seen | set(man["metadata"])
    if actual_files != expected:
        fail("file membership mismatch: extra=%s missing=%s" % (sorted(actual_files - expected), sorted(expected - actual_files)))
    if actual_dirs != set(man["directories"]):
        fail("directory membership mismatch")
    # The seal's owned_files count includes the two metadata files.
    if len(actual_files) != seal["owned_files"] or len(actual_dirs) != seal["owned_directories"]:
        fail("count mismatch")
    total = 0
    for e in man["files"]:
        full = os.path.join(root, e["path"])
        if os.path.getsize(full) != e["size"] or sha(full) != e["sha256"]:
            fail("content mismatch " + e["path"])
        total += e["size"]
    rec = {
        "result": "AUTHENTICATED_INTEGRITY_ONLY",
        "anchor": anchor,
        "seal_size": len(seal_bytes),
        "manifest_sha256": seal["manifest_sha256"],
        "owned_files_including_metadata": len(actual_files),
        "payload_files": len(seen),
        "owned_directories": len(actual_dirs),
        "directories": sorted(actual_dirs),
        "payload_bytes": total,
        "status": seal["status"],
        "scope_sha256": seal["scope_sha256"],
        "files": [{"path": e["path"], "size": e["size"], "sha256": e["sha256"]} for e in man["files"]],
    }
    text = json.dumps(rec, indent=1, sort_keys=True) + "\n"
    if out == "-":
        sys.stdout.write(text)
    else:
        with open(out, "x") as f:
            f.write(text)
        print("AUTHENTICATED", len(actual_files), "files", len(actual_dirs), "dirs", total, "bytes")


if __name__ == "__main__":
    main()
