#!/usr/bin/env python3
"""SS(m,q,l) counterexample hunt v2.
Template: alpha_i = i; f_{ij} = (i+j) mod m (q=m-1: bijection onto !=i);
arm edge at position t>=2: base color (i + t*j + (t-1)) mod m  [linear].
Then greedy repair on arm-internal edges (t>=2) to kill violated pairs.
D exact for n<=1200, formula m+q+ceil(log2 l)-1 (validated) otherwise."""
import json, os, sys, datetime, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scan_trees import D_of
from ss_counter import ss_build, verify_cf

def base_color(m, q, l, i, j, t):
    if t == 1:
        return (i + j) % m
    return (i + t * j + (t - 1)) % m

def make_coloring(m, q, l, k):
    nv, E, ae = ss_build(m, q, l)
    col = [0] * len(E)
    for idx, (i, j, t) in ae.items():
        col[idx] = base_color(m, q, l, i, j, t) % k
    for idx, (a, b) in enumerate(E):
        if a == 0 and b <= m:
            col[idx] = b - 1
    return nv, E, ae, col

def repair(m, q, l, k, max_iters=30000, seed=1):
    nv, E, ae, col = make_coloring(m, q, l, k)
    free = [idx for idx, (i, j, t) in ae.items() if t >= 2]
    rng = random.Random(seed)
    def viol_count():
        return len(verify_cf(nv, E, col))
    bad = verify_cf(nv, E, col)
    cur = len(bad)
    it = 0
    # path index: edge -> pairs containing it (for targeted repair)
    while cur > 0 and it < max_iters:
        it += 1
        u, v = bad[rng.randrange(len(bad))]
        # path u..v: get edge list via BFS
        adj = [[] for _ in range(nv)]
        for i2, (a, b) in enumerate(E):
            adj[a].append((b, i2)); adj[b].append((a, i2))
        # find path u->v
        from collections import deque
        prev = {u: (-1, -1)}
        dq = deque([u])
        while dq and v not in prev:
            x = dq.popleft()
            for w, ei in adj[x]:
                if w not in prev:
                    prev[w] = (x, ei); dq.append(w)
        # reconstruct
        path_edges = []
        x = v
        while x != u:
            p, ei = prev[x]; path_edges.append(ei); x = p
        cands = [ei for ei in path_edges if ei in free]
        if not cands:
            bad = verify_cf(nv, E, col); cur = len(bad); continue
        ei = cands[rng.randrange(len(cands))]
        old = col[ei]
        bestc, bestv = old, cur
        for c in rng.sample(range(k), k):
            if c == old:
                continue
            col[ei] = c
            nv2 = len(verify_cf(nv, E, col))
            if nv2 < bestv:
                bestv, bestc = nv2, c
                if nv2 == 0:
                    break
        col[ei] = bestc
        if bestv < cur:
            bad = verify_cf(nv, E, col); cur = bestv
        else:
            # random perturbation
            ei2 = free[rng.randrange(len(free))]
            col[ei2] = rng.randrange(k)
            bad = verify_cf(nv, E, col); cur = len(bad)
        if it % 200 == 0:
            print(f"    repair iter {it}: violations={cur}", flush=True)
    return col, cur, it

def main():
    out = {"generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(), "cases": []}
    cases = [(8, 7, 4, 8), (9, 8, 4, 9), (10, 9, 8, 10), (12, 11, 16, 13), (16, 15, 32, 17)]
    for (m, q, l, k) in cases:
        nv, E, ae = ss_build(m, q, l)
        if nv <= 1200:
            D = D_of(nv, E)
            Dsrc = "exact"
        else:
            D = m + q + (l - 1).bit_length() - 1
            Dsrc = "formula(validated)"
        Delta = max(m, q + 1)
        L = (nv - 1).bit_length()
        rec = {"m": m, "q": q, "l": l, "k": k, "n": nv, "D": D, "D_source": Dsrc,
               "Delta": Delta, "L": L, "2max": 2 * max(Delta, L),
               "risk": D >= 2 * max(Delta, L)}
        print(json.dumps(rec), flush=True)
        if rec["risk"]:
            col, cur, it = repair(m, q, l, k)
            rec["repair_iters"] = it
            rec["final_violations"] = cur
            if cur == 0:
                W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
                os.makedirs(W, exist_ok=True)
                with open(os.path.join(W, f"cf-coloring-SS-{m}-{q}-{l}-k{k}.json"), "w") as f:
                    json.dump({"family": f"SS({m},{q},{l})", "k_colors": k, "n": nv,
                               "D_exact_or_validated": D, "Delta": Delta,
                               "edge_colors": list(col), "edges": [list(e) for e in E],
                               "verified": "all-pairs CF check, 0 violations"}, f)
                rec["COUNTEREXAMPLE_COLORING_FOUND"] = True
                print("  >>> COUNTEREXAMPLE CERTIFICATE SAVED", flush=True)
        out["cases"].append(rec)
    W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
    os.makedirs(W, exist_ok=True)
    with open(os.path.join(W, "ss-counterexp.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("DONE", datetime.datetime.now(datetime.timezone.utc).isoformat())

if __name__ == "__main__":
    main()
