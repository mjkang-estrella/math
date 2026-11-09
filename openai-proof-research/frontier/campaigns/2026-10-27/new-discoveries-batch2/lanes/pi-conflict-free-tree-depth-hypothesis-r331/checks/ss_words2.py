#!/usr/bin/env python3
"""Exact word-based CF-coloring solver for SS(m, m-1, l), general k >= m.

Model (exact, WLOG alpha_i = i via color permutation):
  For each branch i: choose f-set F_i subset of colors\\{i}, |F_i| = m-1,
  and for each phi in F_i a word W^i_phi (length l, W[0] = phi) s.t.:
  (D) word valid: every contiguous subword has a unique color;
  (C) {i} + W^i_phi[1..t] unique for all t;
  (A) same branch: for all phi!=psi in F_i, all s,t: W[1..s]+V[1..t] unique;
  (B) cross branch i!=i', phi in F_i, psi in F_{i'}: for all s,t:
      W[1..s]+V[1..t]+{i,i'} unique.
DFS with wall-clock budget; SAT cert / UNSAT / TIMEOUT.
"""
import json, os, sys, datetime, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ss_counter import ss_build, verify_cf
from scan_trees import D_of

def valid_words(k, l, first, alpha=None):
    out = []
    def rec(w):
        n = len(w)
        if n == l:
            out.append(tuple(w)); return
        for c in range(k):
            if c == w[-1]:
                continue
            w.append(c)
            ok = True
            for st in range(n + 1):
                cnts = [0] * k
                for x in w[st:]:
                    cnts[x] += 1
                if 1 not in cnts:
                    ok = False; break
            if ok and alpha is not None:
                cnts = [0] * k
                cnts[alpha] += 1
                for x in w[1:]:
                    cnts[x] += 1
                if 1 not in cnts:
                    ok = False
            if ok:
                rec(w)
            w.pop()
    rec([first])
    return out

_prefix_cache = {}
def prefixes(w, k):
    r = _prefix_cache.get((w, k))
    if r is None:
        r = []
        v = [0] * k
        for x in w:
            v = list(v); v[x] += 1; r.append(tuple(v))
        _prefix_cache[(w, k)] = r
    return r

_pc = {}
import os as _os
if _os.environ.get("SS_NOMEMO"):
    def compat(w1, w2, k, l, extras):
        p1 = prefixes(w1, k); p2 = prefixes(w2, k)
        ex = [0] * k
        for e in extras:
            ex[e] += 1
        ex = tuple(ex)
        for s in range(l):
            for t in range(l):
                if 1 not in [x + y + z for x, y, z in zip(p1[s], p2[t], ex)]:
                    return False
        return True
def compat(w1, w2, k, l, extras):
    key = (w1, w2, extras)
    r = _pc.get(key)
    if r is None:
        p1 = prefixes(w1, k); p2 = prefixes(w2, k)
        ex = [0] * k
        for e in extras:
            ex[e] += 1
        ex = tuple(ex)
        r = True
        for s in range(l):
            a = p1[s]
            for t in range(l):
                tot = [x + y + z for x, y, z in zip(a, p2[t], ex)]
                if 1 not in tot:
                    r = False; break
            if not r:
                break
        if len(_pc) < 3_000_000:
            _pc[key] = r
    return r

def solve(m, l, k, deadline):
    dom = {}
    for i in range(m):
        for phi in range(k):
            if phi == i:
                dom[(i, phi)] = []
                continue
            dom[(i, phi)] = valid_words(k, l, phi, alpha=i)
    var_order = [(i, phi) for i in range(m) for phi in range(k) if phi != i]
    assign = {}
    stats = {"nodes": 0}
    rem = {i: sum(1 for (a, p) in var_order if a == i) for i in range(m)}
    cnt = {i: 0 for i in range(m)}

    def dfs(vi):
        stats["nodes"] += 1
        if time.monotonic() > deadline:
            raise TimeoutError
        if vi == len(var_order):
            return all(cnt[i] == m - 1 for i in range(m))
        i, phi = var_order[vi]
        rem[i] -= 1
        try:
            # option 1: skip (phi not in F_i) -- only when k > m, and branch can still reach m-1
            if k > m and cnt[i] < m - 1 and cnt[i] + rem[i] >= m - 1:
                if dfs(vi + 1):
                    return True
            # option 2: assign a word
            if cnt[i] < m - 1:
                for w in dom[(i, phi)]:
                    ok = True
                    for (i2, phi2), v in assign.items():
                        ex = () if i2 == i else (i, i2)
                        if not compat(w, v, k, l, ex):
                            ok = False; break
                    if ok:
                        # (E): W[1..s] + {i,i2} unique for all i2 != i, all s
                        p1 = prefixes(w, k)
                        for i2 in range(m):
                            if i2 == i:
                                continue
                            ex = [0] * k; ex[i] += 1; ex[i2] += 1
                            for s in range(l):
                                tot = [x + y for x, y in zip(p1[s], ex)]
                                if 1 not in tot:
                                    ok = False; break
                            if not ok:
                                break
                    if ok:
                        assign[(i, phi)] = w
                        cnt[i] += 1
                        if dfs(vi + 1):
                            return True
                        cnt[i] -= 1
                        del assign[(i, phi)]
        finally:
            rem[i] += 1
        return False

    try:
        r = dfs(0)
    except TimeoutError:
        return "TIMEOUT", stats
    except RecursionError:
        return "TIMEOUT", stats
    return (dict(assign) if r else None), stats

def words_to_coloring(m, l, words):
    nv, E, ae = ss_build(m, m - 1, l)
    col = [0] * len(E)
    for idx, (a, b) in enumerate(E):
        if a == 0 and b <= m:
            col[idx] = b - 1
    # arms of branch i are interchangeable: assign sorted(F_i)[j] to arm j
    F = {}
    for (i, phi) in words:
        F.setdefault(i, []).append(phi)
    for i in F:
        F[i] = sorted(F[i])
    for idx, (i, j, t) in ae.items():
        phi = F[i][j]
        col[idx] = words[(i, phi)][t - 1]
    return nv, E, col

def main():
    import sys as _s
    lo = int(_s.argv[1]) if len(_s.argv) > 1 else 0
    hi = int(_s.argv[2]) if len(_s.argv) > 2 else 10**9
    out = {"generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(), "cases": []}
    cases = [
        (3, 2, 4, 15), (3, 2, 5, 15), (3, 2, 6, 15),
        (4, 4, 4, 15), (4, 4, 5, 30), (4, 4, 6, 40),
        (3, 4, 3, 15), (3, 4, 4, 15), (3, 4, 5, 30),
        (3, 8, 4, 15), (3, 8, 5, 30), (3, 8, 6, 30),
        (5, 4, 5, 30), (5, 4, 6, 40),
        (4, 8, 5, 40), (4, 8, 6, 40),
        (2, 16, 4, 20), (3, 16, 4, 30), (3, 16, 5, 40),
        (4, 16, 5, 40), (4, 16, 6, 40),
        (3, 32, 5, 40), (3, 32, 6, 40),
        (6, 4, 6, 40), (6, 4, 7, 40),
    ]
    cases = cases[lo:hi]
    for (m, l, k, budget) in cases:
        nv, E, ae = ss_build(m, m - 1, l)
        D = D_of(nv, E) if nv <= 1200 else m + (m - 1) + (l - 1).bit_length() - 1
        Delta = m
        L = (nv - 1).bit_length()
        need = D // 2
        rec = {"m": m, "l": l, "k": k, "n": nv, "D": D, "Delta": Delta, "L": L,
               "need_cfc_le": need, "decisive": k <= need}
        if k < m:
            rec["result"] = "skip k<m"
            out["cases"].append(rec); print(json.dumps(rec), flush=True); continue
        r, stats = solve(m, l, k, time.monotonic() + budget)
        rec["nodes"] = stats["nodes"]
        if r == "TIMEOUT":
            rec["result"] = "TIMEOUT"
        elif r is None:
            rec["result"] = f"UNSAT cfc > {k}"
        else:
            rec["result"] = f"SAT cfc <= {k}"
            nv2, E2, col = words_to_coloring(m, l, r)
            bad = verify_cf(nv2, E2, col)
            rec["tree_violations"] = len(bad)
            rec["verified"] = len(bad) == 0
            if rec["verified"] and k <= need:
                W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
                os.makedirs(W, exist_ok=True)
                with open(os.path.join(W, f"CERT-SS-{m}-{m-1}-{l}-k{k}.json"), "w") as f:
                    json.dump({"family": f"SS({m},{m-1},{l})", "k": k, "n": nv, "D": D,
                               "words": {f"{i},{p}": list(w) for (i, p), w in r.items()},
                               "edge_colors": list(col), "edges": [list(e) for e in E2]}, f)
                rec["COUNTEREXAMPLE"] = True
                print("  >>> COUNTEREXAMPLE CERTIFICATE", flush=True)
        print(json.dumps({k2: rec[k2] for k2 in rec if k2 != 'words'}), flush=True)
        out["cases"].append(rec)
    W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
    os.makedirs(W, exist_ok=True)
    with open(os.path.join(W, "ss-word-solver.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("DONE", datetime.datetime.now(datetime.timezone.utc).isoformat())

if __name__ == "__main__":
    main()
