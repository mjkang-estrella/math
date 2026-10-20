#!/usr/bin/env python3
"""Fetch pinned source blobs and authenticate them against the complete tree.

Usage: python -B fetch.py --project PROJECT --root ROOT PREFIX [PREFIX ...]

Every blob under each path prefix listed in sources/preprints-tree.json is
downloaded from the pinned raw GitHub URL, checked against its Git blob SHA1
and size, and written below ROOT/packet/private/source/. A receipt with the
SHA256 of each body is written to ROOT/packet/private/source/receipts.json.
"""
import argparse
import hashlib
import json
import pathlib
import urllib.request

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--project", required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--skip-pdf", action="store_true")
    ap.add_argument("prefixes", nargs="+")
    a = ap.parse_args()
    project = pathlib.Path(a.project)
    root = pathlib.Path(a.root)
    tree_bytes = (project / "sources/preprints-tree.json").read_bytes()
    if hashlib.sha256(tree_bytes).hexdigest() != TREE_SHA256:
        raise SystemExit("tree hash mismatch")
    tree = json.loads(tree_bytes)
    if tree.get("truncated") is not False or len(tree["tree"]) != 13223:
        raise SystemExit("tree is not the complete listing")
    out = root / "packet/private/source"
    receipts_path = out / "receipts.json"
    receipts = json.loads(receipts_path.read_text()) if receipts_path.exists() else []
    have = {r["path"] for r in receipts}
    for e in tree["tree"]:
        if e["type"] != "blob" or not any(e["path"].startswith(p) for p in a.prefixes):
            continue
        if a.skip_pdf and e["path"].endswith(".pdf"):
            continue
        if e["path"] in have:
            continue
        url = f"https://raw.githubusercontent.com/openai/math/{PIN}/{e['path']}"
        data = urllib.request.urlopen(url, timeout=60).read()
        if git_blob_sha1(data) != e["sha"] or len(data) != e["size"]:
            raise SystemExit(f"authentication failed: {e['path']}")
        dest = out / e["path"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        receipts.append({
            "path": e["path"], "url": url, "git_blob_sha1": e["sha"],
            "size": e["size"], "sha256": hashlib.sha256(data).hexdigest(),
        })
        print("ok", e["path"])
    receipts.sort(key=lambda r: r["path"])
    out.mkdir(parents=True, exist_ok=True)
    receipts_path.write_text(json.dumps(receipts, indent=1) + "\n")


if __name__ == "__main__":
    main()
