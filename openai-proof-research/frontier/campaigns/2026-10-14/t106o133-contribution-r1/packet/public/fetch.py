#!/usr/bin/env python3
"""Fetch pinned openai/math blobs and authenticate them against the complete tree.

Usage: python -B fetch.py --project PROJECT --root ROOT PREFIX [PREFIX ...]

Each blob under a listed path prefix in sources/preprints-tree.json is fetched from
the pinned raw GitHub URL, checked against its Git blob SHA1 and size, and written
below ROOT/packet/private/source/. receipts.json records the SHA256 of each body.
PDFs are skipped.
"""
import argparse
import hashlib
import json
import pathlib
import urllib.request

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"


def blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--project", required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("prefixes", nargs="+")
    a = ap.parse_args()
    tree_bytes = (pathlib.Path(a.project) / "sources/preprints-tree.json").read_bytes()
    if hashlib.sha256(tree_bytes).hexdigest() != TREE_SHA256:
        raise SystemExit("tree hash mismatch")
    tree = json.loads(tree_bytes)
    if tree.get("truncated") is not False or len(tree["tree"]) != 13223:
        raise SystemExit("tree is not the complete listing")
    out = pathlib.Path(a.root) / "packet/private/source"
    rpath = out / "receipts.json"
    receipts = json.loads(rpath.read_text()) if rpath.exists() else []
    have = {r["path"] for r in receipts}
    for e in tree["tree"]:
        p = e["path"]
        if e["type"] != "blob" or p.endswith(".pdf") or p in have:
            continue
        if not any(p.startswith(x) for x in a.prefixes):
            continue
        url = f"https://raw.githubusercontent.com/openai/math/{PIN}/{p}"
        data = urllib.request.urlopen(url, timeout=60).read()
        if blob_sha1(data) != e["sha"] or len(data) != e["size"]:
            raise SystemExit(f"authentication failed: {p}")
        dest = out / p
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        receipts.append({"path": p, "url": url, "git_blob_sha1": e["sha"],
                         "size": e["size"], "sha256": hashlib.sha256(data).hexdigest()})
        print("ok", p)
    receipts.sort(key=lambda r: r["path"])
    rpath.parent.mkdir(parents=True, exist_ok=True)
    rpath.write_text(json.dumps(receipts, indent=1) + "\n")


if __name__ == "__main__":
    main()
