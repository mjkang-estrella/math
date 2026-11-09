#!/usr/bin/env python3
"""Independent reviewer code (rlmexc-review-r1).

Usage: python3 -I target_dfs.py NMIN NMAX OUTJSON

For each n in [NMIN, NMAX], enumerate EVERY pi in S_n with
    RLMv(pi) = R := {1, n-4, n-2, n-1}   and   EXCv(pi) = E := [n] minus R
by a depth-first search over positions 1..n.  The pruning is exact and uses only
the definitions (not the candidate's lemmas P1/P2 or steps 1-3):
  * placing value v at position i is an excedance-value event iff v > i, so we
    require (v > i) == (v in E);
  * an unused excedance value u must still be placeable at a position < u,
    so u > i is required when position i is next (exact feasibility test);
  * the values after position i are exactly the still-unused values, so v is an
    RLM value iff every unused value other than v exceeds v; we require that
    this holds iff v in R.
Both tests are necessary and, at a complete permutation, sufficient, so the
search is complete.  Each solution is then re-checked from scratch with
definition-level brute-force EXCv/RLMv, inv is counted directly, and the cycle
type is computed.  For k = 1..6 the coefficient of x_R y_E in the raw sum and in
F_{n,k} = (-1)^(n-1) * raw is reported.
"""
import json
import sys


def excv(p):
    return frozenset(p[j] for j in range(len(p)) if p[j] > j + 1)


def rlmv(p):
    n = len(p)
    return frozenset(p[i] for i in range(n) if all(p[i] < p[j] for j in range(i + 1, n)))


def inv(p):
    n = len(p)
    return sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])


def cycle_type(p):
    n = len(p)
    seen = [False] * (n + 1)
    lens = []
    for s in range(1, n + 1):
        if not seen[s]:
            L, x = 0, s
            while not seen[x]:
                seen[x] = True
                x = p[x - 1]
                L += 1
            lens.append(L)
    return sorted(lens, reverse=True)


def solve(n):
    R = {1, n - 4, n - 2, n - 1}
    E = set(range(1, n + 1)) - R
    sols = []
    nodes = [0]

    def rec(i, prefix, unused):
        nodes[0] += 1
        if i > n:
            sols.append(tuple(prefix))
            return
        # exact feasibility: an unused value u in E will sit at some position j >= i
        # and needs j < u, so u > i is necessary.
        if any(u in E and u <= i for u in unused):
            return
        for v in sorted(unused):
            if (v > i) != (v in E):
                continue
            is_rlm = all(u > v for u in unused if u != v)
            if is_rlm != (v in R):
                continue
            unused.remove(v)
            prefix.append(v)
            rec(i + 1, prefix, unused)
            prefix.pop()
            unused.add(v)

    rec(1, [], set(range(1, n + 1)))
    rows = []
    for p in sols:
        assert excv(p) == frozenset(E) and rlmv(p) == frozenset(R)
        ct = cycle_type(p)
        rows.append({"perm": list(p), "tail_pos_n-5_to_n-1": list(p[n - 6:n - 1]),
                     "inv": inv(p), "sign": -1 if inv(p) % 2 else 1,
                     "cycle_type": ct, "min_cycle": ct[-1]})
    coeffs = {}
    for k in range(1, 7):
        raw = sum(r["sign"] for r in rows if r["min_cycle"] >= k)
        coeffs[str(k)] = {"raw": raw, "vor": (-1) ** (n - 1) * raw}
    return {"n": n, "R": sorted(R), "E": sorted(E), "dfs_nodes": nodes[0],
            "num_solutions": len(rows), "solutions": rows, "coefficients_by_k": coeffs}


def symbolic_tail(n, row):
    # express the tail in terms of n for comparison with the candidate's table
    names = {1: "1", n - 4: "n-4", n - 3: "n-3", n - 2: "n-2", n: "n"}
    return "(" + ", ".join(names[v] for v in row["tail_pos_n-5_to_n-1"]) + ")"


def main():
    a, b, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    allres = []
    for n in range(a, b + 1):
        r = solve(n)
        prefix_ok = all(row["perm"][i] == i + 2 for row in r["solutions"] for i in range(n - 6)) \
            and all(row["perm"][n - 1] == n - 1 for row in r["solutions"])
        r["forced_prefix_and_last_ok"] = prefix_ok
        r["symbolic_tails"] = sorted(symbolic_tail(n, row) + " type=" + str(row["cycle_type"])
                                     + " sign=" + str(row["sign"]) for row in r["solutions"])
        allres.append(r)
        print("n", n, "solutions", r["num_solutions"], "nodes", r["dfs_nodes"],
              "prefix/last forced", prefix_ok,
              "coef k=3 vor", r["coefficients_by_k"]["3"]["vor"],
              "raw", r["coefficients_by_k"]["3"]["raw"],
              "| vor by k:", [r["coefficients_by_k"][str(k)]["vor"] for k in range(1, 7)], flush=True)
        if n in (a, b):
            for t in r["symbolic_tails"]:
                print("   ", t, flush=True)
    tails_stable = len({tuple(x["symbolic_tails"][i].split(" type")[0] for i in range(len(x["symbolic_tails"])))
                        for x in allres}) == 1
    print("symbolic tail set identical for all n:", tails_stable)
    with open(out, "w") as f:
        json.dump({"results": allres, "symbolic_tail_set_identical": tails_stable}, f, indent=1)


if __name__ == "__main__":
    main()
