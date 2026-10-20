#!/usr/bin/env python3
"""Fetch pinned upstream files into this review root, authenticated against the
complete preprint tree (same scheme as the author's fetch.py)."""
import hashlib, json, os, sys, urllib.request, datetime

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
TREE = os.path.join(ROOT, "sources", "preprints-tree.json")
TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"


def main():
    out = sys.argv[1]
    paths = sys.argv[2:]
    raw = open(TREE, "rb").read()
    assert hashlib.sha256(raw).hexdigest() == TREE_SHA256, "tree hash mismatch"
    tree = {e["path"]: e for e in json.loads(raw)["tree"]}
    os.makedirs(out, exist_ok=True)
    rec_path = os.path.join(out, "receipts.json")
    recs = json.load(open(rec_path)) if os.path.exists(rec_path) else []
    for p in paths:
        e = tree[p]
        url = f"https://raw.githubusercontent.com/openai/math/{PIN}/{p}"
        data = urllib.request.urlopen(url, timeout=60).read()
        blob = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
        ok = blob == e["sha"] and len(data) == e["size"]
        name = p.replace("/", "__")
        with open(os.path.join(out, name), "wb") as f:
            f.write(data)
        recs.append({"path": p, "url": url, "git_blob_sha1": blob, "tree_sha1": e["sha"],
                     "size": len(data), "sha256": hashlib.sha256(data).hexdigest(),
                     "authenticated": ok,
                     "retrieved_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()})
        print(("OK " if ok else "MISMATCH ") + p)
    with open(rec_path, "w") as f:
        json.dump(recs, f, indent=1)


if __name__ == "__main__":
    main()
