#!/usr/bin/env python3
"""Myeongjin Kang; no affiliation. Original code MIT.

Read-only identity verifier for the B8C package. No network, subprocesses,
mathematical diagnostics, repairs, writes, or acceptance gates.
Supply the detached seal SHA256 from OUTSIDE this directory.
"""
import argparse
import hashlib
import json
import stat
import sys
from pathlib import Path, PurePosixPath

SCOPE = "133c0d45fdd9f4a1c328dee664b142ac2cf09c6d0600fcc1ed53bdb565dea838"
STATUS = "FULL_PROOF_CANDIDATE_B8C_AWAITING_INDEPENDENT_REVIEW"
COMMIT = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
METADATA = ["manifest.json", "seal.json"]


def need(condition, reason):
    if not condition:
        raise ValueError(reason)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seal-sha256", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent

    seal_path = root / "seal.json"
    need(not seal_path.is_symlink(), "seal symlink")
    seal_bytes = seal_path.read_bytes()
    need(sha(seal_bytes) == args.seal_sha256.strip().lower(), "external seal anchor mismatch")
    seal = json.loads(seal_bytes)
    need(seal.get("metadata") == METADATA, "seal metadata")
    need(seal.get("scope_sha256") == SCOPE, "seal scope")
    need(seal.get("status") == STATUS, "seal status")

    manifest_bytes = (root / "manifest.json").read_bytes()
    need(len(manifest_bytes) == seal["manifest_size"], "manifest size")
    need(sha(manifest_bytes) == seal["manifest_sha256"], "manifest hash")
    manifest = json.loads(manifest_bytes)
    need(manifest.get("metadata") == METADATA, "manifest metadata")
    need(manifest.get("upstream_commit") == COMMIT, "manifest commit")

    listed = {}
    for entry in manifest["files"]:
        p = entry["path"]
        pp = PurePosixPath(p)
        need(not pp.is_absolute() and ".." not in pp.parts and p not in METADATA, "unsafe path " + p)
        need(p not in listed, "duplicate path " + p)
        listed[p] = entry

    actual_files, actual_dirs = set(), {"."}
    for path in root.rglob("*"):
        mode = path.lstat().st_mode
        need(not stat.S_ISLNK(mode), "symlink " + str(path))
        rel = path.relative_to(root).as_posix()
        if stat.S_ISDIR(mode):
            actual_dirs.add(rel)
        elif stat.S_ISREG(mode):
            actual_files.add(rel)
        else:
            raise ValueError("special file " + rel)

    need(actual_files == set(listed) | set(METADATA), "file membership")
    need(actual_dirs == set(manifest["directories"]), "directory membership")
    need(len(actual_files) == seal["owned_files"], "owned file count")
    need(len(actual_dirs) == seal["owned_directories"], "owned directory count")

    for p, entry in listed.items():
        data = (root / p).read_bytes()
        need(len(data) == entry["size"], "size " + p)
        need(sha(data) == entry["sha256"], "hash " + p)
    need(listed["original-scope.md"]["sha256"] == SCOPE, "scope hash")

    print("VERIFIED %d files (%d payload + %d metadata), %d directories"
          % (len(actual_files), len(listed), len(METADATA), len(actual_dirs)))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        sys.stderr.write("REJECT: %s\n" % exc)
        sys.exit(1)
