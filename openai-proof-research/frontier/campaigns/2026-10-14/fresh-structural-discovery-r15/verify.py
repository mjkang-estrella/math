#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang
# MIT License
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
"""Read-only artifact verification; no mathematical acceptance gate."""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(root, name):
    p = PurePosixPath(name)
    require(isinstance(name, str) and name and not p.is_absolute(), "unsafe path")
    require(all(x not in ("", ".", "..") for x in p.parts), "unsafe path")
    require(str(p) == name, "noncanonical path")
    return root.joinpath(*p.parts)


def main():
    require(len(sys.argv) == 2 and re.fullmatch(r"[0-9a-f]{64}", sys.argv[1]),
            "one external seal SHA256 is required")
    root = Path(__file__).resolve().parent
    seal_bytes = (root / "seal.json").read_bytes()
    require(sha256(seal_bytes) == sys.argv[1], "external seal anchor mismatch")
    seal = json.loads(seal_bytes)
    manifest_bytes = (root / "manifest.json").read_bytes()
    require(len(manifest_bytes) == seal["manifest_size"], "manifest size mismatch")
    require(sha256(manifest_bytes) == seal["manifest_sha256"], "manifest hash mismatch")
    manifest = json.loads(manifest_bytes)
    require(manifest["metadata"] == ["manifest.json", "seal.json"], "metadata mismatch")
    require(seal["metadata"] == manifest["metadata"], "seal metadata mismatch")
    records = manifest["files"]
    names = [r["path"] for r in records]
    require(len(names) == len(set(names)), "duplicate payload path")
    require(not set(names).intersection(manifest["metadata"]), "metadata in payload")
    actual_files, actual_dirs = set(), {"."}
    for current, dirs, files in os.walk(root, followlinks=False):
        current = Path(current)
        for name in dirs + files:
            child = current / name
            require(not child.is_symlink(), "symlink forbidden")
        for name in dirs:
            actual_dirs.add((current / name).relative_to(root).as_posix())
        for name in files:
            child = current / name
            require(child.is_file(), "nonregular entry")
            actual_files.add(child.relative_to(root).as_posix())
    require(actual_files == set(names) | set(manifest["metadata"]), "file membership mismatch")
    require(actual_dirs == set(manifest["directories"]), "directory membership mismatch")
    roles = {"inputs": {"files": 0, "bytes": 0}, "outputs": {"files": 0, "bytes": 0}}
    for record in records:
        path = safe_path(root, record["path"])
        role = "inputs" if record["path"].startswith("inputs/") else "outputs"
        require(record["role"] == role, "role mismatch")
        data = path.read_bytes()
        require(len(data) == record["size"], "size mismatch: " + record["path"])
        require(sha256(data) == record["sha256"], "hash mismatch: " + record["path"])
        roles[role]["files"] += 1
        roles[role]["bytes"] += len(data)
    require(roles == manifest["roles"], "role totals mismatch")
    require(len(actual_files) == seal["owned_files"], "file count mismatch")
    require(len(actual_dirs) == seal["owned_directories"], "directory count mismatch")
    scope_hash = sha256((root / "original-scope.md").read_bytes())
    require(scope_hash == "dc98c7a1b62d7a44ead17140b057e82fdfc5e42083c01b3f679fcf3782e4345c",
            "frozen scope mismatch")
    status = json.loads((root / "status.json").read_bytes())
    require(status["status"] == "UNRESOLVED_FULL_LR" and status["newAccepted"] == 4,
            "research status mismatch")
    for key in ("counted", "independent_mathematical_pass", "independent_contribution_pass",
                "substantial_nomination", "mathematical_program_run", "manuscript_or_lean_package"):
        require(status[key] is False, "unsupported acceptance claim")
    require(status["scope_sha256"] == scope_hash, "status scope mismatch")
    upstream = json.loads((root / "inputs/context/upstream.json").read_bytes())
    require(upstream["commit"] == "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb", "upstream mismatch")
    tree = json.loads((root / "inputs/context/preprints-tree.json").read_bytes())
    require(tree["truncated"] is False and len(tree["tree"]) == 13223, "tree mismatch")
    blobs = {x["path"]: x for x in tree["tree"] if x["type"] == "blob"}
    pinned = json.loads((root / "inputs/pinned-records.json").read_bytes())
    for record in pinned:
        data = safe_path(root, record["local"]).read_bytes()
        identity = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(identity == record["git_blob"] == blobs[record["path"]]["sha"], "Git blob mismatch")
        require(len(data) == record["size"] == blobs[record["path"]]["size"], "pinned size mismatch")
        require(sha256(data) == record["sha256"], "pinned SHA256 mismatch")
    print(json.dumps({"result": "INTEGRITY_OK_ONLY", "research_status": status["status"],
                      "owned_files": len(actual_files), "owned_directories": len(actual_dirs),
                      "payload_bytes": sum(r["size"] for r in records), "roles": roles,
                      "pinned_blobs": len(pinned), "files_written": 0,
                      "live_external_files_read": 0, "mathematical_program_run": False}, sort_keys=True))


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as error:
        print("INTEGRITY_REJECT: " + str(error), file=sys.stderr)
        sys.exit(1)
