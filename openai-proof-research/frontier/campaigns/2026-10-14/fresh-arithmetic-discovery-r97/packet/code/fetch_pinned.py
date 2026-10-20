#!/usr/bin/env python3
"""Fetch pinned upstream blobs and authenticate them against the complete preprints tree."""
import hashlib, json, sys, urllib.request, pathlib
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
ROOT = pathlib.Path(__file__).resolve().parents[1]
PROJECT = ROOT.parents[4]
TREE = PROJECT / "sources" / "preprints-tree.json"
OUT = ROOT / "private" / "upstream"
REG = ROOT / "private" / "fetch-log.jsonl"

def main(paths):
    tree = {it["path"]: it for it in json.loads(TREE.read_text())["tree"]}
    with REG.open("a") as log:
        for p in paths:
            it = tree[p]
            url = f"https://raw.githubusercontent.com/openai/math/{PIN}/{p}"
            data = urllib.request.urlopen(url, timeout=60).read()
            blob = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
            ok = blob == it["sha"] and len(data) == it["size"]
            dest = OUT / p
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            rec = {"path": p, "url": url, "git_blob": blob, "tree_blob": it["sha"],
                   "size": len(data), "sha256": hashlib.sha256(data).hexdigest(), "match": ok}
            log.write(json.dumps(rec) + "\n")
            print(ok, p)
            if not ok:
                sys.exit(1)

if __name__ == "__main__":
    main(sys.argv[1:])
