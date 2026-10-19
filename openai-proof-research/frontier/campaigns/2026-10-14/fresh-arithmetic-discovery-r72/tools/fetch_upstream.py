#!/usr/bin/env python3
"""Fetch pinned OpenAI/math blobs, verify Git blob SHA against the complete
preprints tree, record SHA256. Usage: fetch_upstream.py TREE_JSON OUTDIR RECEIPTS path..."""
import hashlib, json, os, sys, urllib.request
REV = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
tree_path, outdir, receipts_path, *paths = sys.argv[1:]
tree = {e["path"]: e for e in json.load(open(tree_path))["tree"]}
rec = json.load(open(receipts_path)) if os.path.exists(receipts_path) else []
done = {r["path"] for r in rec if r.get("status") == "ok"}
for p in paths:
    if p in done: continue
    url = f"https://raw.githubusercontent.com/openai/math/{REV}/{p}"
    e = tree.get(p)
    r = {"path": p, "url": url}
    if e is None:
        r["status"] = "not-in-tree"; rec.append(r); continue
    try:
        data = urllib.request.urlopen(url, timeout=60).read()
    except Exception as ex:
        r["status"] = f"retrieval-failed: {ex}"; rec.append(r); continue
    blob = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
    r.update(tree_blob=e["sha"], computed_blob=blob, size=len(data),
             sha256=hashlib.sha256(data).hexdigest(),
             status="ok" if blob == e["sha"] else "BLOB-MISMATCH")
    if r["status"] == "ok":
        dest = os.path.join(outdir, p.replace("/", "__"))
        open(dest, "wb").write(data)
        r["local"] = os.path.relpath(dest, os.path.dirname(receipts_path))
    rec.append(r)
json.dump(rec, open(receipts_path, "w"), indent=1)
for r in rec: print(r["status"], r["path"])
