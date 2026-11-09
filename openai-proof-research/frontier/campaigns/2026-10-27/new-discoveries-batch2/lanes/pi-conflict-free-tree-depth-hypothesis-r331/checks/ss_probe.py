#!/usr/bin/env python3
"""SS(m,q,l) star-of-spiders: exact D via tree solver; exact cfc via general
backtracking for small n. Risk zone = D >= 2*max(Delta, ceil(log2 n))."""
import json, os, sys, datetime
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scan_trees import D_of, has_cf_coloring, canon

def ss_tree(m, q, l):
    """center 0; branches b_i; each branch: spider with q arms of l edges
    hanging off b_i.  n = 1 + m*(q*l+1)."""
    edges = []
    nxt = 1
    bs = []
    for i in range(m):
        bs.append(nxt); nxt += 1
    for b in bs:
        edges.append((0, b))
        for j in range(q):
            prev = b
            for t in range(l):
                edges.append((prev, nxt)); prev = nxt; nxt += 1
    return nxt, tuple(edges)

def main():
    out = {"generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat()}
    # D formula check vs exact solver
    checks = []
    for (m, q, l) in [(2,3,2),(3,2,2),(3,3,2),(4,3,2),(4,4,2),(5,4,2),(3,3,4),(2,5,4),(6,5,2),(7,6,2),(8,7,2),(5,5,4),(4,4,8)]:
        n, e = ss_tree(m, q, l)
        Dex = D_of(n, e)
        Df = m + q + (l - 1).bit_length()  # m + q + ceil(log2 l)
        Delta = max(m, q + 1)
        L = (n - 1).bit_length()
        checks.append({"m": m, "q": q, "l": l, "n": n, "D_exact": Dex, "D_formula": Df,
                       "match": Dex == Df, "Delta": Delta, "L": L,
                       "2max": 2 * max(Delta, L), "risk": Dex >= 2 * max(Delta, L)})
        print(checks[-1])
    out["D_checks"] = checks
    # exact cfc on small instances
    cfc_res = []
    for (m, q, l) in [(3,2,2),(4,3,2),(5,4,2),(6,5,2),(3,3,2),(4,4,2),(3,3,4),(5,5,2),(2,4,4)]:
        n, e = ss_tree(m, q, l)
        if n > 80:
            continue
        Delta = max(m, q + 1)
        L = (n - 1).bit_length()
        lo = max(Delta, L)
        # find exact cfc: smallest k with a coloring
        cfc = None
        for k in range(lo, lo + 4):
            if has_cf_coloring(n, e, k):
                cfc = k
                break
        cfc_res.append({"m": m, "q": q, "l": l, "n": n, "Delta": Delta, "L": L,
                        "cfc": cfc, "D": m + q + (l - 1).bit_length()})
        print(cfc_res[-1], flush=True)
    out["cfc_small"] = cfc_res
    W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
    os.makedirs(W, exist_ok=True)
    with open(os.path.join(W, "ss-small.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("DONE")

if __name__ == "__main__":
    main()
