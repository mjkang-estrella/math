#!/usr/bin/env python3
"""Verifier for lane pi-rainbow-path-replication-hypothesis-r317.

Compares SHA256 of every file listed in manifest.json against the fixed recorded
hashes. Covers all payload files and both source bindings (the arXiv PDF and the
arXiv abstract page hashes recorded in sources/source-hashes.txt are themselves
manifest entries, and are additionally cross-checked here by exact literal hash).
Exits 0 only if every comparison matches; any missing file, read error, or hash
mismatch exits nonzero.
"""
import hashlib
import json
import os
import sys

# Fixed source-binding hashes (arXiv:1201.5340 v1 retrieval of 2026-10-30T22:52:00Z)
SOURCE_BINDINGS = {
    "sources/1201.5340.pdf":      "31fb974c75371a4e21be9d35c2f1a04778e470a791399a903798266c60b47f99",
    "sources/1201.5340.abs.html": "b20d0f7ef35ff9ffa335e7f849f1c4a18a1239dbc145c9b70c6ddfbe1be577e1",
    "sources/1201.5340.txt":      "435617f67fedace7dbacc6d1229619fd6274a4db00561332c0f1dbb5d0dc537a",
}

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()

def main():
    failures = []
    try:
        with open("manifest.json", "r", encoding="utf-8") as f:
            man = json.load(f)
    except Exception as e:
        print("FATAL: cannot read manifest.json: %s" % e)
        return 2
    files = man.get("files", {})
    if not files:
        print("FATAL: manifest has no files")
        return 2
    for path, expected in sorted(files.items()):
        if not os.path.isfile(path):
            failures.append("MISSING %s" % path)
            continue
        try:
            actual = sha256(path)
        except Exception as e:
            failures.append("READERROR %s: %s" % (path, e))
            continue
        if actual != expected:
            failures.append("MISMATCH %s: expected %s got %s" % (path, expected, actual))
    # hard source-binding comparison (independent of manifest content)
    for path, expected in SOURCE_BINDINGS.items():
        if path not in files:
            failures.append("BINDING_NOT_IN_MANIFEST %s" % path)
            continue
        if files[path] != expected:
            failures.append("BINDING_HASH_DRIFT %s: manifest %s != fixed %s"
                            % (path, files[path], expected))
        if not os.path.isfile(path) or sha256(path) != expected:
            failures.append("BINDING_FILE_MISMATCH %s" % path)
    if failures:
        print("VERIFY: FAIL (%d)" % len(failures))
        for msg in failures:
            print("  " + msg)
        return 1
    print("VERIFY: OK — %d files matched fixed SHA256 hashes; %d source bindings verified."
          % (len(files), len(SOURCE_BINDINGS)))
    return 0

if __name__ == "__main__":
    sys.exit(main())
