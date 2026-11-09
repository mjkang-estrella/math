"""Enumerate ALL solutions G: Z_L -> {0..3} of G(x)=mex{G[x-a],G[x-b],G[x-c]}
(mod L), via DFS with constraint propagation. Reports minimal periods of all
solutions and whether any has minimal period dividing NO pairwise sum.

Necessary conditions used for pruning:
  - G(x) != G(x-s) for all x, s in S (else G(x) would appear in its own mex set).
  - If some s == 0 mod L: no solution at all.
"""
import sys, json
from functools import lru_cache


def min_period_of(t):
    L = len(t)
    for p in range(1, L + 1):
        if L % p == 0 and all(t[i] == t[i + p] for i in range(L - p)):
            return p
    return L


def enumerate_solutions(S, L, node_cap=30_000_000):
    a, b, c = S
    if any(s % L == 0 for s in S):
        return {"solutions": [], "note": "s == 0 mod L"}
    residues = [((x - a) % L, (x - b) % L, (x - c) % L) for x in range(L)]
    assign = [None] * L
    sols = []
    nodes = [0]
    exhausted = [False]
    # constraint x becomes fully checkable at step t_x = max(residues[x] ++ [x])
    check_at = {}
    for x in range(L):
        check_at.setdefault(max(max(residues[x]), x), []).append(x)

    def check_constraint(x):
        vals = {assign[r] for r in residues[x]}
        i = 0
        while i in vals:
            i += 1
        return assign[x] == i

    def dfs(pos):
        nodes[0] += 1
        if nodes[0] > node_cap:
            exhausted[0] = True
            return
        if pos == L:
            if all(check_constraint(x) for x in range(L)):
                sols.append(tuple(assign))
            return
        to_check = check_at.get(pos, [])
        for v in range(4):
            assign[pos] = v
            # immediate coloring prune: G(pos) != G(pos - s) for all s
            ok = True
            for s in (a, b, c):
                r = (pos - s) % L
                if assign[r] == v:
                    ok = False
                    break
            if ok and all(check_constraint(x) for x in to_check):
                dfs(pos + 1)
            assign[pos] = None
            if exhausted[0]:
                return

    dfs(0)
    return {"solutions": sols, "note": "node_cap_exceeded" if exhausted[0] else "complete",
            "nodes": nodes[0]}


def main():
    a, b, c, Lmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    S = (a, b, c)
    sums = (a + b, b + c, c + a)
    report = []
    print("[", flush=True)
    for L in range(1, Lmax + 1):
        r = enumerate_solutions(S, L)
        if r is None:
            continue
        pers = sorted({min_period_of(t) for t in r["solutions"]})
        bad = [p for p in pers if all(s % p for s in sums)]
        # Ward gcd characterization on each solution
        import math
        gcd_bad = []
        for t in r["solutions"]:
            m = min_period_of(t)
            divs = [s for s in sums if s % m == 0]
            if divs and math.gcd(*divs) != m:
                gcd_bad.append((m, divs, t))
        report.append({"L": L, "n_solutions": len(r["solutions"]), "min_periods": pers,
                       "bad_periods": bad, "gcd_failures": len(gcd_bad),
                       "note": r.get("note", ""), "nodes": r.get("nodes", 0)})
        print(json.dumps(report[-1]) + ",", flush=True)
    print(json.dumps({"S": list(S), "sums": list(sums), "by_L": report}, indent=1))


if __name__ == "__main__":
    main()
