#!/usr/bin/env python3
"""Fetch pinned raw files and authenticate them against the complete preprint tree (git blob SHA-1 + size)."""
import datetime
import hashlib
import json
import pathlib
import sys
import urllib.request

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
ROOT = pathlib.Path(__file__).resolve().parents[2]
PROJ = ROOT.parents[3]
TREE = PROJ / "sources" / "preprints-tree.json"
OUT = ROOT / "packet" / "private" / "upstream"
LOG = ROOT / "work" / "acquisition-log.jsonl"


def main(paths):
    tree = {e["path"]: e for e in json.loads(TREE.read_text())["tree"]}
    for p in paths:
        e = tree[p]
        url = f"https://raw.githubusercontent.com/openai/math/{PIN}/{p}"
        data = urllib.request.urlopen(url, timeout=60).read()
        blob = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
        ok = blob == e["sha"] and len(data) == e["size"]
        if ok:
            dest = OUT / p
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
        rec = {"path": p, "url": url, "size": len(data), "git_blob": blob,
               "tree_sha": e["sha"], "sha256": hashlib.sha256(data).hexdigest(),
               "authenticated": ok,
               "utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
        with LOG.open("a") as f:
            f.write(json.dumps(rec) + "\n")
        print(("OK " if ok else "FAIL ") + p)


if __name__ == "__main__":
    main(sys.argv[1:])
