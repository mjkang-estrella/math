"""Record sha256 of every file under the frozen read-only inputs. Usage: python3 -I hash_frozen.py OUT.json"""
import hashlib, json, os, sys, datetime
BASE = "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31"
ROOTS = ["expanded-corpus-r49", "paley-config-source-review-r1", "paley-config-fidelity-review-r1/review.json",
         "paley-config-fidelity-review-r1/REVIEW.md", "paley-config-parent-integration-r1/ADJUDICATION.json",
         "fresh-corpus-r10/sources/registry-preprints.json"]
def h(p):
    d = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""): d.update(b)
    return d.hexdigest()
out = {}
for r in ROOTS:
    p = os.path.join(BASE, r)
    if os.path.isfile(p): out[r] = h(p); continue
    for dp, dn, fn in os.walk(p):
        dn[:] = [x for x in dn if x not in (".lake", "__pycache__")]
        for f in fn:
            q = os.path.join(dp, f)
            if os.path.islink(q) or not os.path.isfile(q): continue
            out[os.path.relpath(q, BASE)] = h(q)
agg = hashlib.sha256(json.dumps(out, sort_keys=True).encode()).hexdigest()
json.dump({"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "n_files": len(out), "aggregate_sha256": agg, "files": out},
          open(sys.argv[1], "w"), indent=1, sort_keys=True)
print(len(out), agg)
