#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only, external-anchor identity verification. No mathematical verdict.

Original review helper by the TS132 contribution reviewer. Exact-membership
design follows the campaign convention; this implementation is written here.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import re
import sys

AUTHOR = "2fabba39b9b907f675c01162eae65b970236923ed5b14b611017a515f7eef267"
SCOPE = "4f4f5103561d77dd475a5b8f50bbcd0d8989e102c18392ace80cb0b52a735984"
PROOF = "e1e93a97ddae2d47d32feb0fa464da93c32d4de661c93b63ac0e7ff785de310a"
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(value):
    require(isinstance(value, str), "nonstring path")
    path = PurePosixPath(value)
    require(value and not path.is_absolute() and ".." not in path.parts,
            "unsafe path")
    require(str(path) == value and value != ".", "noncanonical path")
    return value


def check_packet(root, anchor):
    require(re.fullmatch(r"[0-9a-f]{64}", anchor) is not None,
            "invalid external anchor")
    manifest_path = root / "manifest.json"
    require(not root.is_symlink() and not manifest_path.is_symlink(),
            "symlink root or manifest")
    raw = manifest_path.read_bytes()
    require(sha(raw) == anchor, "external anchor mismatch")
    obj = json.loads(raw)
    rows = obj["files"]
    listed = [safe_path(row["path"]) for row in rows]
    directories = [safe_path(x) for x in obj["directories"]]
    require(len(listed) == len(set(listed)), "duplicate file")
    require(len(directories) == len(set(directories)), "duplicate directory")
    require("manifest.json" not in listed, "manifest is not payload")
    actual_files, actual_dirs = set(), set()
    for path in root.rglob("*"):
        require(not path.is_symlink(), "symlink forbidden")
        rel = path.relative_to(root).as_posix()
        if path.is_file():
            actual_files.add(rel)
        elif path.is_dir():
            actual_dirs.add(rel)
        else:
            raise ValueError("nonregular entry")
    require(actual_files == set(listed) | {"manifest.json"},
            "file membership mismatch")
    require(actual_dirs == set(directories), "directory membership mismatch")
    for row in rows:
        data = (root / row["path"]).read_bytes()
        require(len(data) == row["bytes"] and sha(data) == row["sha256"],
                "payload mismatch: " + row["path"])
    return len(rows), len(directories)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--anchor", required=True,
                        help="SHA256 manifest anchor supplied outside this packet")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    count, dirs = check_packet(root, args.anchor)
    author = root / "inputs/author"
    author_count, _ = check_packet(author, AUTHOR)
    require(sha((author / "original-scope.md").read_bytes()) == SCOPE,
            "scope anchor mismatch")
    require(sha((author / "candidate.md").read_bytes()) == PROOF,
            "candidate anchor mismatch")

    upstream = json.loads((root / "inputs/context/1-upstream.json").read_text())
    require(upstream["commit"] == PIN, "source pin mismatch")
    tree_bytes = (root / "inputs/context/2-preprints-tree.json").read_bytes()
    tree = json.loads(tree_bytes)
    require(tree["truncated"] is False, "truncated source catalogue")
    paths = [x["path"] for x in tree["tree"]]
    require(len(paths) == len(set(paths)), "duplicate tree paths")
    mapping = {x["path"]: x for x in tree["tree"]}
    receipt = json.loads((author / "source-receipt.json").read_text())
    require(receipt["pin"] == PIN and receipt["complete_tree_truncated"] is False,
            "source receipt mismatch")
    require(sha(tree_bytes) == receipt["complete_tree_sha256"],
            "complete catalogue hash mismatch")
    require(len(receipt["files"]) == 7, "source file count")
    prefix = "preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/"
    inventory = [{"path": x["path"], "type": x["type"], "sha": x["sha"]}
                 for x in tree["tree"]
                 if x["path"].startswith(prefix) and x["type"] == "blob"]
    require(sorted(inventory, key=lambda x: x["path"]) ==
            sorted(receipt["family_inventory"], key=lambda x: x["path"]),
            "family inventory mismatch")
    for row in receipt["files"]:
        data = (author / safe_path(row["local"])).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(sha(data) == row["sha256"] and blob == row["git_blob"],
                "source bytes mismatch")
        require(mapping[row["path"]]["sha"] == blob, "source tree mismatch")
        require("/" + PIN + "/" in row["url"], "unpinned source URL")
    for row in json.loads((author / "private/primary-receipts.json").read_text()):
        data = (author / safe_path(row["file"])).read_bytes()
        require(len(data) == row["bytes"] and sha(data) == row["sha256"],
                "author primary receipt mismatch")
    for row in json.loads((root / "private/primary/retrieval.json").read_text()):
        data = (root / "private/primary" / (row["name"] + ".pdf")).read_bytes()
        require(len(data) == row["size"] and sha(data) == row["sha256"],
                "additional primary receipt mismatch")
    for row in json.loads((root / "context-receipt.json").read_text()):
        require(sha((root / safe_path(row["copy"])).read_bytes()) == row["sha256"],
                "context receipt mismatch")
    print(json.dumps({"status": "IDENTITY_ONLY_OK", "payloads": count,
                      "directories": dirs, "author_payloads": author_count,
                      "pinned_blobs": 7, "primary_pdfs": 5,
                      "scope_sha256": SCOPE, "candidate_sha256": PROOF},
                     sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("IDENTITY_CHECK_FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
