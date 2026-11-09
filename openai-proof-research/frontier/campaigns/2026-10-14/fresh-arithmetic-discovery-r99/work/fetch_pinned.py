#!/usr/bin/env python3
"""Fetch pinned upstream files, check them against the complete preprint tree, log receipts."""
import datetime, hashlib, json, os, sys, urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROJECT = os.path.abspath(os.path.join(ROOT, "..", "..", "..", ".."))
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE = os.path.join(PROJECT, "sources", "preprints-tree.json")
DEST = os.path.join(ROOT, "private", "upstream")
LOG = os.path.join(ROOT, "work", "fetch-log.jsonl")


def blob_sha(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main(paths):
    entries = {e["path"]: e for e in json.load(open(TREE))["tree"]}
    for path in paths:
        e = entries[path]
        url = f"https://raw.githubusercontent.com/openai/math/{PIN}/{path}"
        data = urllib.request.urlopen(url, timeout=60).read()
        ok = blob_sha(data) == e["sha"] and len(data) == e["size"]
        out = os.path.join(DEST, path)
        os.makedirs(os.path.dirname(out), exist_ok=True)
        if ok:
            with open(out, "wb") as f:
                f.write(data)
        rec = {
            "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "url": url, "path": path, "tree_blob": e["sha"], "size": e["size"],
            "got_blob": blob_sha(data), "sha256": hashlib.sha256(data).hexdigest(),
            "blob_match": ok,
        }
        with open(LOG, "a") as f:
            f.write(json.dumps(rec) + "\n")
        print(("OK  " if ok else "BAD ") + path)


if __name__ == "__main__":
    main(sys.argv[1:])
