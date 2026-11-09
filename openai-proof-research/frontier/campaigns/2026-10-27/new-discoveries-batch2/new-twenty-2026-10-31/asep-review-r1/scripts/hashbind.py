#!/usr/bin/env python3
"""Hash-bind the read-only inputs of the 368807 review. usage: hashbind.py OUT.json"""
import hashlib, json, os, sys, datetime
L = "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r96"
items = ["ASEP-COUNTEREXAMPLE.md", "VALIDATION.md", "results.json", "raw/368807.jsonl", "extracted.json",
         "lean-replay-3/result.json", "logs/resource-incident-ghv.txt", "SHA256SUMS.json", "SUMMARY.md"]
dirs = ["sources", "scripts", "outputs/asep", "lean"]
files = []
for i in items: files.append(i)
for d in dirs:
    for root, _, fs in os.walk(os.path.join(L, d)):
        if "/lean/build" in root: continue
        for f in fs:
            p = os.path.relpath(os.path.join(root, f), L)
            if d == "sources" and not (p.startswith("sources/368807") or "2511.05045" in p or "2506.10671" in p or p.startswith("sources/prior")):
                continue
            files.append(p)
out = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "base": L, "files": {}}
for p in sorted(set(files)):
    with open(os.path.join(L, p), "rb") as fh:
        b = fh.read()
    out["files"][p] = {"sha256": hashlib.sha256(b).hexdigest(), "bytes": len(b)}
json.dump(out, open(sys.argv[1], "w"), indent=1)
print(len(out["files"]), "files hashed")
