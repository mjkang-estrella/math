"""Group order-9 hits into isomorphism classes; locate G; summarise all ext/gen stats."""
import json, sys, glob
sys.path.insert(0, sys.argv[1])
from search import canon, ir_info, classify, connected
logs = sys.argv[2]
files = sorted(glob.glob(logs + "/ext9-*.json"))
hits = []; stats = {}; ev = 0; ranges = []
for f in files:
    d = json.load(open(f)); hits += d["hits"]; ev += d["evaluated"]; ranges.append((d["lo"], d["hi"]))
    for k, v in d["stats"].items(): stats[k] = stats.get(k, 0) + v
ranges.sort()
cover = ranges[0][0] == 0 and all(ranges[i][1] == ranges[i+1][0] for i in range(len(ranges)-1)) and ranges[-1][1] == 12346
classes = {}
for h in hits:
    k = canon(9, h["adj"]); classes.setdefault(k, []).append(h)
G_edges = [tuple(int(c) for c in s) for s in "03 04 06 07 13 15 16 17 18 24 25 27 28 36 38 46 47 48 57 58".split()]
adjG = [0] * 9
for a, b in G_edges: adjG[a] |= 1 << b; adjG[b] |= 1 << a
kG = canon(9, adjG)
out = {"chunk_files": [f.split("/")[-1] for f in files], "ranges_cover_0_12346": cover, "evaluated": ev,
       "evaluated_expected": 12346 * 256, "stats": stats, "n_hits": len(hits), "n_classes": len(classes), "classes": []}
for k, hs in classes.items():
    h = hs[0]
    adj = h["adj"]
    E = [(a, b) for a in range(9) for b in range(a + 1, 9) if adj[a] >> b & 1]
    degs = sorted(bin(x).count("1") for x in adj)
    out["classes"].append({"type": h["type"], "IR": h["IR"], "labelled_hits": len(hs), "connected": h["connected"],
        "n_edges": len(E), "degrees": degs, "edges": ["%d%d" % e for e in E], "is_G": k == kG})
out["G_IR_info"] = ir_info(9, adjG)[:2]
print(json.dumps(out, indent=1))
