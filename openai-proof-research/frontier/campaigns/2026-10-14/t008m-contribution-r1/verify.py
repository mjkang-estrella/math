#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only external-anchor identity verifier for the T008M contribution review.

Authenticates bytes and exact inventory only. No mathematical inference.
"""
import argparse
import hashlib
import json
import os
import re
import stat
import sys
from pathlib import Path

FORMAT = "t008m-contribution-r1-exact-v1"
AUTHOR_DIR = "fresh-arithmetic-discovery-r28"
AUTHOR_ANCHORS = {
    "manifest.json": "2a476225d2df44641e62313dfa3653fb26820879b1dc55537d0ec7a7b8e77a19",
    "verify.py": "f69ed2552d049fd35ae0bfc8089eb53aca3a7763c3f7a99f4acf56d8e794164e",
    "candidate-008.md": "0bf87bcaaef27e9cb5d5d2451a5808f1f09b41022f2c03aeecbc33d76f2fba5f",
    "scope-008.md": "8ad29468d11619f3108690f025fc71b4a47c9d55cb6faa7ad3565fa7885a9039",
}
TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
FAMILY = "preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/"
FAMILY_BLOBS = 15
FAMILY_NON_PDF = 14


class Fail(Exception):
    pass


def require(condition, message):
    if not condition:
        raise Fail(message)


def read_nofollow(path):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        st = os.fstat(fd)
        require(stat.S_ISREG(st.st_mode), "nonregular file: " + str(path))
        require(st.st_nlink == 1, "hardlink forbidden: " + str(path))
        chunks = []
        while True:
            chunk = os.read(fd, 1 << 20)
            if not chunk:
                break
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        os.close(fd)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def no_dup(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, "duplicate JSON key: " + key)
        out[key] = value
    return out


def load(data):
    return json.loads(data.decode("utf-8"), object_pairs_hook=no_dup)


def safe(rel):
    require(isinstance(rel, str) and rel and not rel.startswith("/") and "\\" not in rel,
            "unsafe path")
    require(all(part not in ("", ".", "..") for part in rel.split("/")), "unsafe path")
    return rel


def base_dir():
    script = Path(os.path.abspath(__file__))
    for p in [*reversed(script.parents), script]:
        st = os.lstat(p)
        require(not stat.S_ISLNK(st.st_mode), "script/root/ancestor symlink forbidden: " + str(p))
        if p != script:
            require(stat.S_ISDIR(st.st_mode), "non-directory ancestor: " + str(p))
    return script.parent


def scan(root):
    files, dirs = set(), set()

    def walk(directory):
        with os.scandir(directory) as entries:
            for entry in entries:
                path = Path(entry.path)
                rel = safe(path.relative_to(root).as_posix())
                st = os.lstat(path)
                if stat.S_ISLNK(st.st_mode):
                    raise Fail("symlink forbidden: " + rel)
                if stat.S_ISDIR(st.st_mode):
                    dirs.add(rel)
                    walk(path)
                elif stat.S_ISREG(st.st_mode):
                    require(st.st_nlink == 1, "hardlink forbidden: " + rel)
                    files.add(rel)
                else:
                    raise Fail("nonregular object forbidden: " + rel)

    walk(root)
    return files, dirs


def check_rows(root, rows, actual, label):
    require(isinstance(rows, dict), label + " rows invalid")
    require(set(rows) == actual, label + " file inventory mismatch")
    for rel, row in rows.items():
        safe(rel)
        require(isinstance(row, dict) and set(row) == {"bytes", "sha256"}, "invalid row: " + rel)
        require(type(row["bytes"]) is int and re.fullmatch("[0-9a-f]{64}", row["sha256"]),
                "invalid row: " + rel)
        data = read_nofollow(root / rel)
        require(len(data) == row["bytes"] and sha(data) == row["sha256"],
                "payload mismatch: " + rel)


def check_dirs(expected, actual, label):
    require(isinstance(expected, list) and len(expected) == len(set(expected)),
            label + " directory list invalid")
    for rel in expected:
        safe(rel)
    require(set(expected) == actual, label + " directory inventory mismatch")


def git_blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--anchor", required=True,
                        help="manifest SHA256 supplied outside this packet")
    parser.add_argument("--private", action="store_true",
                        help="also require the exact private inventory and receipts")
    parser.add_argument("--source-tree", required=True, type=Path,
                        help="path to the complete sources/preprints-tree.json")
    parser.add_argument("--author-dir", type=Path,
                        help="frozen author packet; default is the sibling " + AUTHOR_DIR)
    args = parser.parse_args()
    require(re.fullmatch("[0-9a-f]{64}", args.anchor) is not None, "invalid anchor format")

    root = base_dir()
    files, dirs = scan(root)
    raw = read_nofollow(root / "manifest.json")
    require(sha(raw) == args.anchor, "external manifest anchor mismatch")
    manifest = load(raw)
    require(set(manifest) == {"format", "public_files", "public_dirs",
                              "private_files", "private_dirs"}, "manifest schema")
    require(manifest["format"] == FORMAT, "manifest format")

    def is_private(rel):
        return rel == "private" or rel.startswith("private/")

    public = {f for f in files if not is_private(f) and f != "manifest.json"}
    check_rows(root, manifest["public_files"], public, "public")
    check_dirs(manifest["public_dirs"], {d for d in dirs if not is_private(d)}, "public")

    provenance = load(read_nofollow(root / "primary-provenance.json"))
    if args.private:
        check_rows(root, manifest["private_files"], {f for f in files if is_private(f)}, "private")
        check_dirs(manifest["private_dirs"], {d for d in dirs if is_private(d)}, "private")
        for row in provenance["stored_in_this_review"]:
            data = read_nofollow(root / safe(row["file"]))
            require(len(data) == row["bytes"] and sha(data) == row["sha256"],
                    "primary receipt mismatch: " + row["file"])

    author = Path(os.path.abspath(args.author_dir)) if args.author_dir else root.parent / AUTHOR_DIR
    require(stat.S_ISDIR(os.lstat(author).st_mode), "author packet missing, symlinked or not a directory")
    for name, expected in AUTHOR_ANCHORS.items():
        require(sha(read_nofollow(author / name)) == expected, "author anchor mismatch: " + name)

    tree_bytes = read_nofollow(args.source_tree)
    require(sha(tree_bytes) == TREE_SHA256, "canonical source tree identity mismatch")
    tree = load(tree_bytes)
    require(tree["truncated"] is False, "truncated source tree")
    family = [r for r in tree["tree"] if r["type"] == "blob" and r["path"].startswith(FAMILY)]
    require(len(family) == FAMILY_BLOBS, "source family blob count")
    non_pdf = [r for r in family if not r["path"].lower().endswith(".pdf")]
    require(len(non_pdf) == FAMILY_NON_PDF, "source family non-PDF count")
    blobs_checked = 0
    if args.private:
        for row in non_pdf:
            local = author / "private" / safe(row["path"][len("preprints/"):])
            require(git_blob(read_nofollow(local)) == row["sha"],
                    "source Git blob mismatch: " + row["path"])
            blobs_checked += 1
        for row in provenance["read_from_author_private_copies"]:
            data = read_nofollow(author / safe(row["author_local"]))
            require(sha(data) == row["sha256"], "author primary copy mismatch: " + row["name"])

    print(json.dumps({
        "status": "IDENTITY_ONLY_OK_NOT_MATHEMATICS",
        "public_files": len(manifest["public_files"]),
        "public_directories": len(manifest["public_dirs"]),
        "private_files_checked": len(manifest["private_files"]) if args.private else 0,
        "private_directories_checked": len(manifest["private_dirs"]) if args.private else 0,
        "author_anchors_checked": len(AUTHOR_ANCHORS),
        "canonical_tree_checked": True,
        "source008_git_blobs_checked": blobs_checked,
    }, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Fail, OSError, ValueError, KeyError, TypeError, UnicodeDecodeError) as error:
        print("IDENTITY_CHECK_FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
