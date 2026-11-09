"""Isomorphism-filtered enumeration of all graphs on n vertices (own code).
Usage: gen.py NMAX
Every graph on n vertices is (an isomorphic copy of) some graph on n-1 vertices plus a new vertex
joined to a subset, so augmenting one representative per class of order n-1 by all 2^(n-1) subsets
and filtering by isomorphism yields exactly one representative per class of order n.
Writes data/all{n}.txt (one upper-triangle code per line) and prints counts."""
import sys, json, time
sys.path.insert(0, "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/scripts")
from mocd import *
D = "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1/data/"
NMAX = int(sys.argv[1])
OEIS_ALL = {1: 1, 2: 2, 3: 4, 4: 11, 5: 34, 6: 156, 7: 1044, 8: 12346}        # A000088
OEIS_CONN = {1: 1, 2: 1, 3: 2, 4: 6, 5: 21, 6: 112, 7: 853, 8: 11117}         # A001349
reps = {1: [[0]]}
res = {}
t0 = time.time()
for n in range(2, NMAX + 1):
    buckets = {}
    out = []
    for base in reps[n - 1]:
        for sub in range(1 << (n - 1)):
            adj = list(base) + [sub]
            for v in range(n - 1):
                if sub >> v & 1:
                    adj[v] |= 1 << (n - 1)
            inv, col = wl_invariant(n, adj)
            lst = buckets.setdefault(inv, [])
            dup = False
            for (a2, c2) in lst:
                if isomorphic(n, adj, col, a2, c2):
                    dup = True
                    break
            if not dup:
                lst.append((adj, col))
                out.append(adj)
    reps[n] = out
    conn = sum(1 for a in out if is_connected_graph(n, a))
    res[n] = {"all": len(out), "connected": conn, "oeis_all": OEIS_ALL[n], "oeis_conn": OEIS_CONN[n],
              "ok": len(out) == OEIS_ALL[n] and conn == OEIS_CONN[n], "elapsed_s": round(time.time() - t0, 2)}
    with open(D + "all%d.txt" % n, "w") as f:
        for a in out:
            f.write("%d\n" % encode(n, a))
    print(n, res[n], flush=True)
res[1] = {"all": 1, "connected": 1, "ok": True}
with open(D + "all1.txt", "w") as f:
    f.write("0\n")
print(json.dumps(res))
