#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Myeongjin Kang; no affiliation.
"""Read-only round-2 identity verifier. An EXTERNAL detached-seal SHA256 is required.

Run with python3 -I -B verify.py --seal-sha256 <external anchor>.
Authenticates bytes before parsing each metadata layer. Executes no payload
code, performs no mathematical diagnostic, and makes no truth judgment.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys

SCOPE = "133c0d45fdd9f4a1c328dee664b142ac2cf09c6d0600fcc1ed53bdb565dea838"
AUTHOR_ANCHOR = "fc997d93ac553767e1ce252e73e57ffb3c675d36b09d1949c1e8a14f6f9db9af"
COMMIT = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
AUTHOR_REL = "frontier/campaigns/2026-10-14/fresh-structural-discovery-r16"
META = ["manifest.json", "seal.json"]


def need(ok, why):
    if not ok:
        raise ValueError(why)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique_pairs(items):
    result = {}
    for key, value in items:
        need(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def parse(data):
    return json.loads(data, object_pairs_hook=unique_pairs)


def member(name, directory=False):
    need(isinstance(name, str) and bool(name), "non-string/empty member")
    if directory and name == ".":
        return name
    need(not any(ord(c) < 32 for c in name), "control character in member")
    need("\\" not in name and ":" not in name and not name.startswith("/"),
         "unsafe member: " + name)
    need(all(c not in ("", ".", "..") for c in name.split("/")),
         "noncanonical member: " + name)
    need("__pycache__" not in name.split("/") and
         not name.endswith((".pyc", ".pyo")), "bytecode member: " + name)
    return name


def safe_ancestors(path):
    for current in [path, *path.parents]:
        mode = current.lstat().st_mode
        need(stat.S_ISDIR(mode) and not stat.S_ISLNK(mode),
             "symlink/non-directory ancestor: " + str(current))


def read(base, name):
    member(name)
    path = base / name
    safe_ancestors(path.parent)
    mode = path.lstat().st_mode
    need(stat.S_ISREG(mode) and not stat.S_ISLNK(mode),
         "symlink/special input: " + str(path))
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    with os.fdopen(fd, "rb") as handle:
        before = os.fstat(handle.fileno())
        data = handle.read()
        after = os.fstat(handle.fileno())
    need((before.st_ino, before.st_dev, before.st_size, before.st_mtime_ns) ==
         (after.st_ino, after.st_dev, after.st_size, after.st_mtime_ns),
         "input changed while reading: " + name)
    return data


def inventory(root):
    safe_ancestors(root)
    files, directories = set(), {"."}
    for base, dirs, names in os.walk(root, followlinks=False):
        for name in dirs + names:
            path = Path(base) / name
            rel = path.relative_to(root).as_posix()
            mode = path.lstat().st_mode
            need(not stat.S_ISLNK(mode), "symlink member: " + rel)
            if stat.S_ISDIR(mode):
                member(rel, directory=True)
                directories.add(rel)
            else:
                member(rel)
                need(stat.S_ISREG(mode), "special member: " + rel)
                files.add(rel)
    return files, directories


def authenticate(root, anchor, expected=None):
    # The seal is hashed before JSON parsing, then authenticates the manifest.
    seal_bytes = read(root, "seal.json")
    need(sha(seal_bytes) == anchor, "external seal anchor mismatch")
    seal = parse(seal_bytes)
    need(seal["metadata"] == META, "seal metadata contract")
    need(seal["scope_sha256"] == SCOPE, "seal scope")
    manifest_bytes = read(root, "manifest.json")
    need(len(manifest_bytes) == seal["manifest_size"] and
         sha(manifest_bytes) == seal["manifest_sha256"],
         "authenticated manifest bytes mismatch")
    manifest = parse(manifest_bytes)
    need(manifest["metadata"] == META, "manifest metadata contract")
    need(manifest["upstream_commit"] == COMMIT, "pinned commit")
    listed = {}
    for entry in manifest["files"]:
        name = member(entry["path"])
        need(name not in listed and name not in META, "duplicate/metadata file")
        need(entry["role"] in ("inputs", "outputs", "tools"), "file role")
        need(type(entry["size"]) is int and entry["size"] >= 0, "file size type")
        need(re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]) is not None,
             "file digest type")
        listed[name] = entry
    directories = [member(x, directory=True) for x in manifest["directories"]]
    need(len(set(directories)) == len(directories), "duplicate directory")
    need(set(manifest["directory_roles"]) == set(directories), "directory roles")
    actual_files, actual_dirs = inventory(root)
    need(actual_files == set(listed) | set(META), "missing/extra file members")
    need(actual_dirs == set(directories), "missing/extra directory members")
    need(len(actual_files) == seal["owned_files"] and
         len(actual_dirs) == seal["owned_directories"], "membership counts")
    if expected:
        need((len(seal_bytes), len(actual_files), len(actual_dirs)) == expected,
             "external package size/count contract")
    for name, entry in listed.items():
        data = read(root, name)
        need(len(data) == entry["size"] and sha(data) == entry["sha256"],
             "payload bytes mismatch: " + name)
    need(sha(read(root, "original-scope.md")) == SCOPE, "frozen scope bytes")
    return manifest, seal


def read_only_audit(event, args):
    if event == "open":
        mode = args[1]
        flags = args[2]
        need(not (isinstance(mode, str) and any(c in mode for c in "wax+")),
             "verifier attempted write")
        need(not (isinstance(flags, int) and
                  flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)),
             "verifier attempted write flags")
    need(event not in {"os.remove", "os.rename", "os.mkdir", "os.rmdir",
                       "os.symlink", "os.link", "os.chmod", "os.truncate",
                       "subprocess.Popen", "os.system", "socket.connect",
                       "socket.bind"}, "forbidden verifier operation: " + event)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seal-sha256", required=True)
    args = parser.parse_args()
    need(re.fullmatch(r"[0-9a-f]{64}", args.seal_sha256) is not None,
         "anchor must be 64 lowercase hex digits")
    root = Path(os.path.abspath(__file__)).parent
    safe_ancestors(root)
    sys.addaudithook(read_only_audit)
    manifest, seal = authenticate(root, args.seal_sha256)
    need(seal["status"] == "CONTRIBUTION_REVIEW_R2_COMPLETE_UNRESOLVED", "seal status")
    status = parse(read(root, "status.json"))
    need(status["counted"] is False and status["mathematics"] == "PASS_FULL_B8C"
         and status["contribution"] == "UNRESOLVED", "status contract")
    need(status["scope_sha256"] == SCOPE, "status scope")
    repo = root.parents[3]
    # These seals authenticate their own metadata before payload parsing.
    authenticate(repo / AUTHOR_REL, AUTHOR_ANCHOR, (416, 35, 8))
    review_rel = "frontier/campaigns/2026-10-14/complex-projector-borsuk-review-r1"
    authenticate(repo / review_rel,
                 "c9527d05aff931a233962ef61a0f2de62d962a5fc3375735ac5afdcacdfaaa44",
                 (440, 30, 5))
    baseline = parse(read(root, "inputs/external-baseline.json"))
    paths, fixed, snapshots = set(), 0, 0
    for entry in baseline["files"]:
        name = member(entry["path"])
        need(name not in paths, "duplicate external path")
        paths.add(name)
        if entry["verification"] == "snapshot-only":
            data = read(root, member(entry["snapshot_path"]))
            snapshots += 1
        else:
            need(entry["verification"] == "fixed-external", "external role")
            data = read(repo, name)
            fixed += 1
        need(len(data) == entry["size"] and sha(data) == entry["sha256"],
             "changed input: " + name)
    need((fixed, snapshots) == (69, 2), "fixed/snapshot counts")
    for name, directories in baseline["directories"].items():
        need(name in ("fresh-structural-discovery-r16",
                      "complex-projector-borsuk-review-r1"), "external root")
        need(len(set(directories)) == len(directories), "duplicate external directory")
        expected = {member(x, directory=True) for x in directories}
        _, actual = inventory(root.parent / name)
        need(actual == expected, "external directory membership")
    tree = parse(read(repo, "sources/preprints-tree.json"))
    need(tree["truncated"] is False and len(tree["tree"]) == 13223,
         "complete catalogue required")
    catalogue = {}
    for entry in tree["tree"]:
        name = member(entry["path"])
        need(name not in catalogue, "duplicate catalogue member")
        catalogue[name] = entry
    records = parse(read(repo, review_rel + "/inputs/pinned-catalogue-check.json"))
    need(len(records["pinned"]) == 14, "pinned count")
    for entry in records["pinned"]:
        data = read(repo, member(entry["local_reference"]))
        git_id = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        original = catalogue[member(entry["path"])]
        need(git_id == entry["git_blob_sha1"] == original["sha"] and
             len(data) == entry["size"] == original["size"], "pinned Git blob mismatch")
    primary = parse(read(root, "inputs/primary-records.json"))
    paths = set()
    for entry in primary["files"]:
        name = member(entry["path"])
        need(name not in paths and name.startswith("inputs/primary/"),
             "duplicate/unsafe primary path")
        paths.add(name)
        data = read(root, name)
        need(len(data) == entry["size"] and sha(data) == entry["sha256"],
             "frozen primary input mismatch")
    need(paths == {e["path"] for e in manifest["files"]
                   if e["path"].startswith("inputs/primary/")}, "primary inventory")
    print(json.dumps({"result": "INTEGRITY_OK_ONLY", "owned_files": seal["owned_files"],
                      "owned_directories": seal["owned_directories"],
                      "fixed_external_files": fixed, "snapshot_only_contexts": snapshots,
                      "author_files": 35, "review_r1_files": 30, "pinned_blobs": 14,
                      "primary_members": len(paths), "writes": 0,
                      "mathematical_program_run": False}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as exc:
        sys.stderr.write("INTEGRITY_REJECT: " + str(exc) + "\n")
        sys.exit(1)
