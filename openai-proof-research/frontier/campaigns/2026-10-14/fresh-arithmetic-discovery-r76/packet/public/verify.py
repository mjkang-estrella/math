#!/usr/bin/env python3
"""Read-only r76 evidence integrity verifier. No mathematical gates. MIT."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def decode(data):
    return json.loads(data, object_pairs_hook=pairs)


def relative(value):
    require(isinstance(value, str) and value, "empty/non-string path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and all(x not in (".", "..", "") for x in value.split("/")), "unsafe path: " + value)
    require("\\" not in value and str(path) == value, "noncanonical path: " + value)
    return value


def inventory(root):
    require(stat.S_ISDIR(root.lstat().st_mode), "packet root must be a real directory")
    files, directories = set(), set()
    for base, dirs, names in os.walk(root, followlinks=False):
        for name in dirs + names:
            path = Path(base) / name
            rel = path.relative_to(root).as_posix()
            mode = path.lstat().st_mode
            require(not stat.S_ISLNK(mode), "symlink: " + rel)
            if stat.S_ISDIR(mode):
                directories.add(rel)
            elif stat.S_ISREG(mode):
                files.add(rel)
            else:
                raise ValueError("nonregular object: " + rel)
    return files, directories


def verify(root, expected):
    require(re.fullmatch(r"[0-9a-f]{64}", expected) is not None, "expected detached SHA256 must be 64 lowercase hex characters")
    files, dirs = inventory(root)
    raw = (root / "manifest.json").read_bytes()
    require(digest(raw) == expected, "detached manifest SHA256 mismatch")
    manifest = decode(raw)
    require(manifest["schema"] == "r76-exact-packet-v1", "manifest schema mismatch")
    require(manifest["upstream_commit"] == PIN, "manifest pin mismatch")
    listed = {}
    for row in manifest["files"]:
        name = relative(row["path"])
        require(name != "manifest.json" and name not in listed, "duplicate/self manifest entry")
        listed[name] = row
    listed_dirs = [relative(name) for name in manifest["directories"]]
    require(len(set(listed_dirs)) == len(listed_dirs), "duplicate directory")
    require(files == set(listed) | {"manifest.json"}, "exact file inventory mismatch")
    require(dirs == set(listed_dirs), "exact directory inventory mismatch")
    for name, row in listed.items():
        data = (root / name).read_bytes()
        require(type(row["bytes"]) is int and row["bytes"] == len(data), "size mismatch: " + name)
        require(row["sha256"] == digest(data), "SHA256 mismatch: " + name)

    def read(name):
        return decode((root / name).read_bytes())

    chosen = read("public/canonical-selection.json")
    require(chosen["commit"] == PIN and chosen["tree_sha256"] == TREE_SHA256, "canonical metadata mismatch")
    entries = {e["path"]: e for e in chosen["entries"]}
    require(len(entries) == len(chosen["entries"]) == 74, "canonical selection duplication/count")
    sources = read("public/source-provenance.json")
    require(len(sources) == 74, "source count mismatch")
    seen, upstream_paths = set(), set()
    for row in sources:
        name = relative(row["path"])
        up = relative(row["upstream_path"])
        require(name == "private/upstream/" + up, "retained source path mismatch")
        require(name not in seen and up not in upstream_paths, "source duplication")
        seen.add(name)
        upstream_paths.add(up)
        require(row["url"] == "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + up, "unpinned/raw URL mismatch")
        data = (root / name).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
        canonical = entries[up]
        require(canonical["type"] == "blob" and canonical["sha"] == row["git_blob"] == blob, "Git blob mismatch: " + name)
        require(canonical["size"] == row["bytes"] == len(data), "source size mismatch")
        require(row["sha256"] == digest(data), "source digest mismatch")
    require(upstream_paths == set(entries), "source/selection coverage mismatch")
    require(seen == {name for name in files if name.startswith("private/upstream/")}, "unreceipted upstream file")
    contexts = read("public/context-receipts.json")
    require(any(r["path"] == "sources/preprints-tree.json" and r["sha256"] == TREE_SHA256 for r in contexts), "complete-tree receipt mismatch")
    primary_files = set()
    successes, failures = 0, 0
    for row in read("public/primary-provenance.json"):
        if "failure" in row:
            require(isinstance(row["failure"], str) and row["failure"], "empty failure receipt")
            failures += 1
            continue
        require(row["conversion_status"] == 0, "failed primary text conversion")
        for ext, key in (("pdf", "pdf_sha256"), ("txt", "text_sha256")):
            name = relative("private/primary/" + row["name"] + "." + ext)
            require(name not in primary_files, "duplicate successful primary receipt")
            primary_files.add(name)
            require(digest((root / name).read_bytes()) == row[key], "primary digest mismatch")
        successes += 1
    require(primary_files == {name for name in files if name.startswith("private/primary/")}, "primary coverage mismatch")
    selection = read("public/selection-status.json")
    require(selection["target_frozen"] is False and selection["nominee"] is None, "unexpected candidate state")
    require(selection["independent_gate_assigned"] is False and selection["campaign_count_assignment"] is None, "unexpected author gate/count")
    return {"status": "INTEGRITY_OK", "manifest_sha256": expected, "packet_files_including_manifest": len(files), "packet_directories": len(dirs), "pinned_source_files": len(sources), "primary_successes": successes, "primary_failures_recorded": failures, "mathematical_gate": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", required=True)
    parser.add_argument("--expected-manifest-sha256", required=True, help="mandatory trusted hash obtained OUTSIDE the packet")
    args = parser.parse_args()
    try:
        result = verify(Path(args.packet).absolute(), args.expected_manifest_sha256)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(json.dumps({"status": "INTEGRITY_FAILURE", "error": str(exc), "mathematical_gate": False}, sort_keys=True))
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
