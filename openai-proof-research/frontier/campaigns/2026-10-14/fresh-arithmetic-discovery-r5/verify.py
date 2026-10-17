#!/usr/bin/env python3
"""Read-only byte verification; MIT, copyright 2026 Myeongjin Kang."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, anchor):
    need(len(anchor) == 64 and all(c in "0123456789abcdef" for c in anchor),
         "invalid external anchor")
    need(not (root / "manifest.json").is_symlink(), "symlink manifest")
    raw = (root / "manifest.json").read_bytes()
    need(sha(raw) == anchor, "manifest hash mismatch")
    manifest = json.loads(raw)
    need(manifest["format"] == "arithmetic-r5-prescreen-v1", "wrong format")
    names = [r["path"] for r in manifest["files"]]
    need(len(names) == len(set(names)), "duplicate path")
    for name in names:
        q = PurePosixPath(name)
        need(name not in ("", ".", "manifest.json") and str(q) == name
             and not q.is_absolute() and ".." not in q.parts and "\\" not in name,
             "unsafe path")
    actual_files, actual_dirs = set(), set()
    for q in root.rglob("*"):
        need(not q.is_symlink(), "symlink payload")
        rel = q.relative_to(root).as_posix()
        if q.is_file():
            actual_files.add(rel)
        elif q.is_dir():
            actual_dirs.add(rel)
        else:
            raise ValueError("nonregular payload")
    need(actual_files == set(names) | {"manifest.json"}, "file inventory mismatch")
    need(actual_dirs == set(manifest["directories"]), "directory inventory mismatch")
    payloads = {}
    for record in manifest["files"]:
        data = (root / record["path"]).read_bytes()
        need(len(data) == record["bytes"] and sha(data) == record["sha256"],
             "payload mismatch: " + record["path"])
        payloads[record["path"]] = data
    sources = json.loads(payloads["source-receipt.json"])
    need(sources["commit"] == "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb", "wrong pin")
    for record in sources["sources"]:
        data = payloads[record["local"]]
        git_blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        need(git_blob == record["git_blob"] and sha(data) == record["sha256"],
             "pinned source mismatch")
    status = json.loads(payloads["status.json"])
    need(status["counted"] is False and status["scope_frozen"] is False
         and status["candidate_nominated"] is False, "status mismatch")
    return {"status":"BYTES_AUTHENTICATED_ONLY", "payloads":len(payloads),
            "pinned_blobs":len(sources["sources"]), "counted":False,
            "scope_frozen":False, "writes":0}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest-sha256", required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(verify(Path(__file__).absolute().parent,
                                args.manifest_sha256), indent=2))
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(1, "VERIFICATION_FAILED: " + str(error) + "\n")
