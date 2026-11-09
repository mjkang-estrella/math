#!/usr/bin/env python3
"""Read-only exact finite diagnostics; not a proof or correctness gate.
Run with python -B. Standard library only. Creates no files.
"""
from fractions import Fraction as F
from itertools import combinations, product
import json


def trees(n, edges):
    result = []
    for chosen in combinations(range(len(edges)), n - 1):
        reached = {0}
        while True:
            more = reached | {v for i in chosen for u, v in
                              (edges[i], edges[i][::-1]) if u in reached}
            if more == reached:
                break
            reached = more
        if len(reached) == n:
            result.append(frozenset(chosen))
    return result


def cuts(n, edges):
    return [frozenset(i for i, (u, v) in enumerate(edges)
                      if bool(mask & (1 << u)) != bool(mask & (1 << v)))
            for mask in range(1, (1 << n) - 1) if mask & 1]


def thinness(tree, x, cutlist):
    return max(F(len(tree & c), 1) / sum(x[i] for i in c) for c in cutlist)


def main():
    edges = list(combinations(range(4), 2))
    tt = trees(4, edges)
    # Independently enumerate the labelled trees via all 16 Pruefer words.
    pp = set()
    for word in product(range(4), repeat=2):
        deg = [1 + word.count(i) for i in range(4)]
        built = []
        for v in word:
            u = next(i for i in range(4) if deg[i] == 1)
            built.append(edges.index(tuple(sorted((u, v)))))
            deg[u] -= 1
            deg[v] -= 1
        rest = tuple(i for i in range(4) if deg[i] == 1)
        built.append(edges.index(rest))
        pp.add(frozenset(built))
    assert set(tt) == pp and len(tt) == 16
    cc = cuts(4, edges)
    assert len(cc) == 7
    x = tuple(F(i, 5) for i in (1, 1, 4, 4, 1, 4))
    ratios = {t: thinness(t, x, cc) for t in tt}
    v = frozenset((2, 3, 5))
    assert min(ratios.values()) == F(15, 13)
    assert {t for t in tt if ratios[t] < F(5, 3)} == {v}
    assert x[5] == F(4, 5) and 5 in v
    mixture = [(F(1, 5), frozenset((0, 2, 5))),
               (F(1, 5), frozenset((1, 3, 4))), (F(3, 5), v)]
    assert all(t in tt and ratios[t] <= F(5, 3) for w, t in mixture)
    assert tuple(sum(w for w, t in mixture if i in t)
                 for i in range(6)) == x
    star = frozenset((0, 1, 2))
    assert star in tt and (frozenset(range(6)) - star) not in tt
    tri = list(combinations(range(3), 2))
    tritrees, tricuts = trees(3, tri), cuts(3, tri)
    triangle_samples = []
    for i in range(1, 30):
        p = F(i, 90)
        y = (1 - p, 1 - p, 2 * p)
        a = [thinness(t, y, tricuts) for t in tritrees]
        assert min(a) == 1 / (1 - p) and max(a) == 2 / (1 + p)
        weights = [1 - y[next(j for j in range(3) if j not in t)]
                   for t in tritrees]
        assert tuple(sum(w for w, t in zip(weights, tritrees) if j in t)
                     for j in range(3)) == y
        triangle_samples.append(str(p))
    print(json.dumps({"kind": "exact finite diagnostics, not a mathematical gate",
                      "K4_trees": 16, "K4_cuts": 7,
                      "K4_single_tree_optimum": "15/13",
                      "K4_exact_marginal_threshold": "5/3",
                      "K4_mixture_weights": [str(w) for w, t in mixture],
                      "triangle_parameters_checked": triangle_samples,
                      "arbitrary_packing_removal_counterexample": True}, indent=2))


if __name__ == "__main__":
    main()
