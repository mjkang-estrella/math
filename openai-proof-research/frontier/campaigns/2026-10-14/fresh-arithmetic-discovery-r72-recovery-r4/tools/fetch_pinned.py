#!/usr/bin/env python3
"""Fetch files from the pinned openai/math revision and record identity receipts.

Usage: fetch_pinned.py PREPRINTS_TREE_JSON OUTDIR RECEIPTS_JSON path [path ...]

Each path is looked up in the complete preprints tree; the downloaded bytes
are accepted only when their Git blob hash equals the tree entry.  Failed
retrievals are recorded, never silently dropped.
"""
import hashlib
import json
import os
import sys
import urllib.request

REV = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def main() -> None:
    tree_path, outdir, receipts_path, *paths = sys.argv[1:]
    raw = json.load(open(tree_path))
    entries = raw["tree"] if isinstance(raw, dict) else raw
    tree = {e["path"]: e for e in entries}
    receipts = json.load(open(receipts_path)) if os.path.exists(receipts_path) else []
    have = {r["path"] for r in receipts if r.get("status") == "ok"}
    os.makedirs(outdir, exist_ok=True)
    for p in paths:
        if p in have:
            continue
        url = f"https://raw.githubusercontent.com/openai/math/{REV}/{p}"
        rec = {"path": p, "url": url}
        entry = tree.get(p)
        if entry is None:
            rec["status"] = "not-in-complete-tree"
            receipts.append(rec)
            continue
        try:
            data = urllib.request.urlopen(url, timeout=90).read()
        except Exception as exc:  # recorded as a failed retrieval
            rec["status"] = f"retrieval-failed: {exc}"
            receipts.append(rec)
            continue
        blob = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
        rec.update(
            tree_blob=entry["sha"],
            computed_blob=blob,
            size=len(data),
            sha256=hashlib.sha256(data).hexdigest(),
            status="ok" if blob == entry["sha"] else "BLOB-MISMATCH",
        )
        if rec["status"] == "ok":
            dest = os.path.join(outdir, p.replace("/", "__"))
            with open(dest, "wb") as fh:
                fh.write(data)
            rec["local"] = os.path.relpath(dest, os.path.dirname(os.path.abspath(receipts_path)))
        receipts.append(rec)
    with open(receipts_path, "w") as fh:
        json.dump(receipts, fh, indent=1)
    for r in receipts:
        print(r["status"], r["path"])


if __name__ == "__main__":
    main()
