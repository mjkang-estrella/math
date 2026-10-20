#!/usr/bin/env python3
"""Fetch pinned openai/math files and authenticate them against the complete
preprints tree (Git blob SHA-1).  Writes only under packet/private/source/.

Usage: fetch.py PATH [PATH ...]   (paths relative to the repository root)
"""
import hashlib, json, os, sys, urllib.request

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
PROJECT = os.path.normpath(os.path.join(ROOT, "..", "..", "..", ".."))
TREE = os.path.join(PROJECT, "sources", "preprints-tree.json")
TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
OUT = os.path.join(ROOT, "packet", "private", "source")
RECEIPTS = os.path.join(OUT, "receipts.json")


def blob_sha1(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main(paths):
    raw = open(TREE, "rb").read()
    assert hashlib.sha256(raw).hexdigest() == TREE_SHA256, "tree hash mismatch"
    tree = json.loads(raw)
    items = tree["tree"] if isinstance(tree, dict) else tree
    index = {it["path"]: it for it in items}
    receipts = json.load(open(RECEIPTS)) if os.path.exists(RECEIPTS) else {}
    for p in paths:
        it = index[p]
        assert it["type"] == "blob", p
        url = "https://raw.githubusercontent.com/openai/math/%s/%s" % (
            PIN, urllib.request.quote(p))
        data = urllib.request.urlopen(url, timeout=60).read()
        sha1 = blob_sha1(data)
        assert sha1 == it["sha"], (p, sha1, it["sha"])
        assert len(data) == it["size"], p
        dest = os.path.join(OUT, p)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        open(dest, "wb").write(data)
        receipts[p] = {"url": url, "git_blob_sha1": sha1, "size": len(data),
                       "sha256": hashlib.sha256(data).hexdigest()}
        print("ok", p, len(data))
    json.dump(receipts, open(RECEIPTS, "w"), indent=1, sort_keys=True)


if __name__ == "__main__":
    main(sys.argv[1:])
