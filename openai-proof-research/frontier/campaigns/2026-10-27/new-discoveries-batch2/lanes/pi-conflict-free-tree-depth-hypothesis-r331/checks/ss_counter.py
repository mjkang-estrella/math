#!/usr/bin/env python3
"""SS(m,q,l): exact D; template coloring with k=m colors; all-pairs CF
verification; randomized offset search.  Risk instances have D=2*Delta:
counterexample iff a k=Delta coloring exists."""
import json, os, sys, datetime, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scan_trees import D_of

def ss_build(m, q, l):
    """Vertex ids: 0 = main center c; 1..m = branch centers b_i;
    arm (i,j) vertex at position t (1..l): id = m+1 + ((i*q+j)*l + t-1)."""
    edges = []          # list of (a,b)
    arm_edges = {}      # edge index -> (i,j,t): t=1 is b--pos1 edge; t in 2..l
    def vid(i, j, t):
        return m + 1 + (i * q + j) * l + (t - 1)
    for i in range(m):
        edges.append((0, i + 1))          # alpha_i
        for j in range(q):
            edges.append((i + 1, vid(i, j, 1)))
            arm_edges[len(edges) - 1] = (i, j, 1)
            for t in range(2, l + 1):
                edges.append((vid(i, j, t - 1), vid(i, j, t)))
                arm_edges[len(edges) - 1] = (i, j, t)
    nv = m + 1 + m * q * l
    return nv, tuple(edges), arm_edges

def make_coloring(m, q, l, k, off):
    """alpha_i = i (0-indexed).  f_{ij} (arm edge t=1) = (i+j) mod m  [requires
    q = m-1 so this is a bijection onto colors != i].
    Arm edge t (t>=2): color = (f_{ij} + off[t-2]) mod k."""
    nv, E, ae = ss_build(m, q, l)
    col = [0] * len(E)
    for idx, (a, b) in enumerate(E):
        if a == 0 and b <= m:
            col[idx] = b - 1
    for idx, (i, j, t) in ae.items():
        F = (i + j) % m
        if t == 1:
            col[idx] = F
        else:
            col[idx] = (F + off[t - 2]) % k
    return nv, E, col

def verify_cf(n, edges, col):
    """All-pairs CF check.  Returns list of violating (u,v), u<v."""
    k = max(col) + 1
    adj = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        adj[a].append((b, i)); adj[b].append((a, i))
    from collections import deque
    bad = []
    for u in range(n):
        cnt0 = [0] * k
        dq = deque([(u, -1, cnt0)])
        seen = {u}
        while dq:
            v, pe, cnt = dq.popleft()
            if v != u and not any(c == 1 for c in cnt):
                bad.append((u, v) if u < v else (v, u))
            for w, ei in adj[v]:
                if ei == pe or w in seen:
                    continue
                seen.add(w)
                c2 = list(cnt); c2[col[ei]] += 1
                dq.append((w, ei, tuple(c2)))
    return bad

def main():
    out = {"generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(), "cases": []}
    cases = [(8, 7, 4, 8), (9, 8, 4, 9), (10, 9, 8, 10), (12, 11, 16, 13), (16, 15, 32, 17), (32, 31, 32, 33)]
    rng = random.Random(20261031)
    for (m, q, l, k) in cases:
        nv, E, ae = ss_build(m, q, l)
        D = D_of(nv, E)
        Delta = max(m, q + 1)
        L = (nv - 1).bit_length()
        rec = {"m": m, "q": q, "l": l, "k": k, "n": nv, "D": D, "Delta": Delta,
               "L": L, "2max": 2 * max(Delta, L), "risk": D >= 2 * max(Delta, L)}
        print(json.dumps(rec), flush=True)
        out["cases"].append(rec)
        if not rec["risk"] or q != m - 1 or k != m:
            rec["note"] = "not attempted" if not rec["risk"] else "template mismatch"
            continue
        if nv > 4000:
            rec["note"] = "too large for O(n^2 k) verify here"
            continue
        best = None; found = None
        for trial in range(600):
            off = tuple(range(1, l)) if trial == 0 else tuple(rng.randrange(k) for _ in range(l - 1))
            nv2, E2, col = make_coloring(m, q, l, k, off)
            bad = verify_cf(nv2, E2, col)
            if best is None or len(bad) < best[0]:
                best = (len(bad), off)
            if not bad:
                found = (off, col)
                break
        rec["trials"] = trial + 1
        rec["best_violations"] = best[0]
        rec["best_off"] = list(best[1])
        if found:
            off, col = found
            W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
            os.makedirs(W, exist_ok=True)
            fn = os.path.join(W, f"cf-coloring-SS-{m}-{q}-{l}-k{k}.json")
            with open(fn, "w") as f:
                json.dump({"family": f"SS({m},{q},{l})", "k_colors": k, "n": nv,
                           "D_exact": D, "Delta": Delta, "offsets": list(off),
                           "edge_colors": list(col), "edges": [list(e) for e in E],
                           "verified": "all-pairs CF check, 0 violations"}, f)
            rec["COUNTEREXAMPLE_COLORING_FOUND"] = True
            print("  >>> k-coloring FOUND => cfc <= k, D >= 2k: COUNTEREXAMPLE certificate", flush=True)
        out["cases"] = [r for r in out["cases"]]
        # update last record
        for r in out["cases"]:
            if r.get("m") == m and r.get("q") == q and r.get("l") == l:
                r.update({k2: v2 for k2, v2 in rec.items()})
        print(json.dumps(rec), flush=True)
    W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
    os.makedirs(W, exist_ok=True)
    with open(os.path.join(W, "ss-counterexp.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("DONE")

if __name__ == "__main__":
    main()
