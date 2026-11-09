#!/usr/bin/env python3
"""Exact word-based CF-coloring solver for SS(m, m-1, l) with k colors.

Model (exact): a CF coloring with k colors, WLOG alpha_i = i (color perm),
corresponds to choosing a word W^i_phi (length l, over k colors) for each
branch i and arm f-value phi != i, with W^i_phi[1] = phi, s.t.:
  (D) every word is valid: every contiguous subword has a unique color
      (paths within one arm);
  (C) for branch i: {i} + W^i_phi[1..t] has a unique color for all t (c-paths);
  (A) same branch i, phi != psi: for all s,t: W[1..s]+V[1..t] unique-colored
      (paths between arms of one branch through b_i);
  (B) cross branch i!=i', phi != i, psi != i': for all s,t:
      W[1..s]+V[1..t]+{i,i'} unique-colored.
These are ALL paths (verified by construction of the path set of SS).
WLOG arm order within a branch is by f-value (arm-block permutation symmetry).

Solver: DFS over (i,phi) with forward checking; complete => certificate
(verify on the concrete tree afterwards).  Exhaustive => UNSAT proof for
cfc > k on this family instance.
"""
import json, os, sys, datetime, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ss_counter import ss_build, verify_cf
from scan_trees import D_of

def valid_words(k, l, first, alpha=None):
    """All words w, w[0]=first, every contiguous subword has a unique color;
    if alpha is not None, also {alpha}+w[1..t] unique for all t (C)."""
    out = []
    def sub_ok(cnts):
        return any(c == 1 for c in cnts)
    def rec(w):
        n = len(w)
        if n == l:
            out.append(tuple(w)); return
        for c in range(k):
            if c == w[-1]:
                continue
            w.append(c)
            ok = True
            # check subwords ending at new position
            for st in range(n + 1):
                cnts = [0] * k
                for x in w[st:]:
                    cnts[x] += 1
                if not sub_ok(cnts):
                    ok = False; break
            if ok and alpha is not None:
                # (C): {alpha} + w[1..t] for t = n+1 (1-indexed length)
                cnts = [0] * k
                cnts[alpha] += 1
                for x in w[1:]:
                    cnts[x] += 1
                if not sub_ok(cnts):
                    ok = False
            if ok:
                rec(w)
            w.pop()
    rec([first])
    return out

def counts_of(word, k, s):
    v = [0] * k
    for x in word[:s]:
        v[x] += 1
    return tuple(v)

def has_unique(*count_vectors):
    tot = None
    for cv in count_vectors:
        if tot is None:
            tot = list(cv)
        else:
            tot = [a + b for a, b in zip(tot, cv)]
    return any(c == 1 for c in tot)

def pair_compat(w1, w2, k, l, extras=()):
    """for all s,t: prefix counts combine (+extras colors) => unique exists."""
    p1 = [counts_of(w1, k, s) for s in range(1, l + 1)]
    p2 = [counts_of(w2, k, s) for s in range(1, l + 1)]
    ex = [0] * k
    for e in extras:
        ex[e] += 1
    for s in range(l):
        for t in range(l):
            if not has_unique(p1[s], p2[t], tuple(ex)):
                return False
    return True

def solve(m, l, k, node_budget=2_000_000, seed_domains=None):
    """Returns dict (i,phi)->word if SAT, None if UNSAT, 'UNKNOWN' if budget."""
    # domains
    dom = {}
    for i in range(m):
        for phi in range(m):
            if phi == i:
                continue
            ws = valid_words(k, l, phi, alpha=i)
            if not ws:
                return None  # (C) unsatisfiable => cfc > k
            dom[(i, phi)] = ws
    order = sorted(dom.keys(), key=lambda x: (x[0], x[1]))
    assign = {}
    nodes = [0]
    # pair memo
    memo = {}
    def compat(i, phi, w, i2, phi2, v):
        key = (w, v, i, i2)
        r = memo.get(key)
        if r is None:
            if i == i2:
                r = pair_compat(w, v, k, l, ())
            else:
                r = pair_compat(w, v, k, l, (i, i2))
            memo[key] = r
        return r
    def dfs(idx):
        nodes[0] += 1
        if nodes[0] > node_budget:
            raise Budget()
        if idx == len(order):
            return True
        i, phi = order[idx]
        for w in dom[(i, phi)]:
            ok = True
            # check against all assigned
            for (i2, phi2), v in assign.items():
                # constraint exists iff the path exists: arms (i,phi),(i2,phi2)
                # same branch: phi != phi2 (distinct f-values, always true here)
                # cross: need phi != i2? arm (i,phi) exists requires phi != i;
                # arm (i2,phi2) requires phi2 != i2. Paths exist for all pairs.
                if not compat(i, phi, w, i2, phi2, v):
                    ok = False; break
            if ok:
                assign[(i, phi)] = w
                if dfs(idx + 1):
                    return True
                del assign[(i, phi)]
        return False
    class Budget(Exception):
        pass
    try:
        r = dfs(0)
    except Budget:
        return "UNKNOWN"
    return dict(assign) if r else None

def main():
    out = {"generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(), "cases": []}
    # decisive instances: (m, l, k) for SS(m, m-1, l)
    cases = [(3, 2, 5), (3, 2, 4), (3, 2, 3), (4, 2, 4), (4, 2, 5), (5, 2, 5), (5, 2, 6), (7, 2, 7), (7, 2, 8), (3, 4, 3), (3, 4, 4), (3, 4, 5), (4, 4, 5), (5, 4, 6), (6, 4, 5), (5, 4, 5), (3, 8, 5), (3, 8, 6), (4, 8, 5), (4, 8, 6), (5, 8, 6), (2, 4, 4), (2, 8, 5), (2, 8, 6)]
    for (m, l, k) in cases:
        nv, E, ae = ss_build(m, m - 1, l)
        D = D_of(nv, E) if nv <= 1200 else m + (m - 1) + (l - 1).bit_length() - 1
        Delta = m
        L = (nv - 1).bit_length()
        need = D // 2  # counterexample iff cfc <= need
        rec = {"m": m, "l": l, "k": k, "n": nv, "D": D, "Delta": Delta, "L": L,
               "need_cfc_le": need, "k_le_need": k <= need}
        if k <= need:
            r = solve(m, l, k, node_budget=400_000)
            if r == "UNKNOWN":
                rec["result"] = "UNKNOWN(budget)"
            elif r is None:
                rec["result"] = f"UNSAT: cfc(SS({m},{m-1},{l})) > {k}"
            else:
                rec["result"] = f"SAT: cfc <= {k} => COUNTEREXAMPLE candidate"
                rec["words"] = {f"{i},{p}": list(w) for (i, p), w in r.items()}
                # build explicit coloring and verify on tree
                col = [-1] * len(E)
                for idx, (a, b) in enumerate(E):
                    if a == 0 and b <= m:
                        col[idx] = b - 1
                def vid(i, j, t):
                    return m + 1 + ((i * (m - 1) + j) * l + t - 1)
                for idx, (a, b) in enumerate(E):
                    pass
                # arm edges: index->(i,j,t) from ss_build? recompute mapping
                nv2, E2, ae2 = ss_build(m, m - 1, l)
                for idx, (i, j, t) in ae2.items():
                    phi = (i + j) % m  # original f-value labeling; need word for (i, phi)
                    w = r[(i, phi)]
                    col[idx] = w[t - 1]
                bad = verify_cf(nv2, E2, col)
                rec["tree_verify_violations"] = len(bad)
                rec["verified_counterexample"] = (len(bad) == 0)
                if len(bad) == 0:
                    W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
                    os.makedirs(W, exist_ok=True)
                    with open(os.path.join(W, f"cf-coloring-SS-{m}-{m-1}-{l}-k{k}.json"), "w") as f:
                        json.dump({"family": f"SS({m},{m-1},{l})", "k": k, "n": nv,
                                   "D": D, "words": {f"{i},{p}": list(w) for (i, p), w in r.items()},
                                   "edge_colors": list(col), "edges": [list(e) for e in E2]}, f)
        else:
            rec["result"] = "k > D/2: not counterexample-relevant (data point only)"
        print(json.dumps({k2: rec[k2] for k2 in rec if k2 != 'words'}), flush=True)
        out["cases"].append(rec)
    W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
    os.makedirs(W, exist_ok=True)
    with open(os.path.join(W, "ss-word-solver.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("DONE", datetime.datetime.now(datetime.timezone.utc).isoformat())

if __name__ == "__main__":
    main()
