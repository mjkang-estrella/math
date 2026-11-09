#!/usr/bin/env python3
"""Hash-bind the read-only review inputs. Usage: hashbind.py OUT.json"""
import hashlib, json, os, sys, datetime
BASE = "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31"
ROOTS = ["xor-magic-root-ruling-r1.json",
         "xor-magic-focused-r1",
         "xor-magic-formal-r1/SUMMARY.md", "xor-magic-formal-r1/GAPS.md", "xor-magic-formal-r1/results.json",
         "xor-magic-formal-r1/formal", "xor-magic-formal-r1/xor-magic-partial-source.zip",
         "xor-magic-formal-r1/statement-correspondence.md",
         "xor-magic-formal-r2/SUMMARY.md", "xor-magic-formal-r2/GAPS.md", "xor-magic-formal-r2/results.json",
         "xor-magic-formal-r2/formal", "xor-magic-formal-r2/xor-magic-r2-partial-source.zip",
         "xor-magic-formal-r2/statement-correspondence.md",
         "expanded-corpus-r90/raw/372205.jsonl", "expanded-corpus-r90/extracted.json",
         "expanded-corpus-r90/sources/2512.19278.abs.html", "expanded-corpus-r90/sources/2512.19278.abs.txt",
         "expanded-corpus-r90/sources/2512.19278.html", "expanded-corpus-r90/sources/2512.19278.txt",
         "expanded-corpus-r90/sources/2512.19278.abs.html.receipt.json", "expanded-corpus-r90/sources/2512.19278.html.receipt.json"]
def h(p):
    d = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""): d.update(b)
    return d.hexdigest()
out = {}
for r in ROOTS:
    p = os.path.join(BASE, r)
    if os.path.isdir(p):
        for dp, dn, fn in os.walk(p):
            dn[:] = sorted(x for x in dn if x != "__pycache__")
            for f in sorted(fn):
                q = os.path.join(dp, f); out[os.path.relpath(q, BASE)] = h(q)
    elif os.path.exists(p): out[r] = h(p)
    else: out[r] = None
agg = hashlib.sha256(json.dumps(out, sort_keys=True).encode()).hexdigest()
json.dump({"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "count": len(out), "aggregate": agg, "files": out}, open(sys.argv[1], "w"), indent=1, sort_keys=True)
print(len(out), agg)
