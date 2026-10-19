#!/usr/bin/env python3
"""MIT. Fetch pinned upstream files into the owned private source directory.

Each path is matched against the complete preprints tree (size and Git blob
SHA1) and a canonical record is appended to private/canonical.json.
Usage: fetch.py PATH [PATH ...]
"""
import hashlib
import json
import os
import sys
import urllib.parse
import urllib.request

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
HERE = os.path.dirname(os.path.abspath(__file__))
PACKET = os.path.dirname(HERE)
ROOT = os.path.dirname(PACKET)
PROJECT = os.path.abspath(os.path.join(ROOT, "..", "..", "..", ".."))
TREE = os.path.join(PROJECT, "sources", "preprints-tree.json")
SRC = os.path.join(PACKET, "private", "source")
CANON = os.path.join(PACKET, "private", "canonical.json")


def blob_sha1(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main(paths):
    tree = json.load(open(TREE))
    index = {e["path"]: e for e in tree["tree"]}
    records = json.load(open(CANON)) if os.path.exists(CANON) else []
    have = {r["record"]["path"] for r in records}
    for path in paths:
        entry = index[path]
        url = "https://raw.githubusercontent.com/openai/math/%s/%s" % (
            PIN, urllib.parse.quote(path))
        data = urllib.request.urlopen(url, timeout=60).read()
        assert len(data) == entry["size"], (path, len(data), entry["size"])
        assert blob_sha1(data) == entry["sha"], path
        dest = os.path.join(SRC, path)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "wb") as fh:
            fh.write(data)
        if path not in have:
            records.append({
                "record": entry, "url": url, "local": "private/source/" + path,
                "sha256": hashlib.sha256(data).hexdigest()})
            have.add(path)
        print("ok", len(data), path)
    records.sort(key=lambda r: r["record"]["path"])
    os.makedirs(os.path.dirname(CANON), exist_ok=True)
    with open(CANON, "w") as fh:
        json.dump(records, fh, indent=1, sort_keys=True)
        fh.write("\n")


if __name__ == "__main__":
    main(sys.argv[1:])
