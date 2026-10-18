#!/usr/bin/env python3
"""Exact finite checks for the T117Q contribution review r2.

These are diagnostics for comparison statements in review.md. They are not
proof dependencies of T117Q and say nothing about the arbitrary-dimension or
all-size theorem. Written independently of the parent's grid_control.py.
"""
from fractions import Fraction
from itertools import product
import json
import math


def linf(x, y):
    return max(abs(a - b) for a, b in zip(x, y))


def cnd_form(points, weights):
    return sum(wi * wj * linf(x, y)
               for x, wi in zip(points, weights) for y, wj in zip(points, weights))


def six_point_certificate():
    pos = [(2, 1, 0), (0, 1, 0), (0, 1, 1)]
    neg = [(1, 0, 1), (1, 0, 0), (1, 2, 0)]
    pts, w = pos + neg, [1, 1, 1, -1, -1, -1]
    assert all(0 <= c <= 2 for p in pts for c in p)
    assert sum(w) == 0
    q = cnd_form(pts, w)
    assert q == 2
    # Zero-padding into a larger grid {0..k}^d keeps the sup metric unchanged.
    padded = [p + (0,) * 4 for p in pts]
    assert cnd_form(padded, w) == q
    return {"side": 2, "dimension": 3, "cnd_quadratic_form": q,
            "negative_type_requires": "<= 0 for zero-sum weights"}


def grid_average(kmax):
    for k in range(1, kmax + 1):
        pairs = (k + 1) ** 2
        avg = Fraction(sum(abs(u - v) for u in range(k + 1) for v in range(k + 1)), pairs)
        assert avg == Fraction(k * (k + 2), 3 * (k + 1))
        assert avg >= Fraction(k, 3)
    # Small full-grid check that E d_inf <= k and the coordinate map keeps >= 1/3.
    rows = []
    for k, d in [(1, 1), (1, 3), (2, 2), (2, 3), (3, 2)]:
        g = list(product(range(k + 1), repeat=d))
        n2 = len(g) ** 2
        e_inf = Fraction(sum(linf(x, y) for x in g for y in g), n2)
        e_first = Fraction(sum(abs(x[0] - y[0]) for x in g for y in g), n2)
        assert e_inf <= k and 3 * e_first >= e_inf
        rows.append({"k": k, "d": d, "avg_dinf": str(e_inf), "avg_first_coordinate": str(e_first)})
    return {"closed_form_checked_up_to_k": kmax, "full_grid_cases": rows}


def petersen_frechet():
    """Illustrates that sup-grids contain graph metrics isometrically (Frechet map)."""
    outer = [(i, (i + 1) % 5) for i in range(5)]
    spokes = [(i, i + 5) for i in range(5)]
    inner = [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    adj = {v: set() for v in range(10)}
    for a, b in outer + spokes + inner:
        adj[a].add(b)
        adj[b].add(a)
    dist = []
    for s in range(10):
        d = {s: 0}
        frontier = [s]
        while frontier:
            nxt = []
            for v in frontier:
                for w in adj[v]:
                    if w not in d:
                        d[w] = d[v] + 1
                        nxt.append(w)
            frontier = nxt
        dist.append([d[t] for t in range(10)])
    diam = max(max(r) for r in dist)
    image = [tuple(dist[x]) for x in range(10)]
    assert all(linf(image[x], image[y]) == dist[x][y] for x in range(10) for y in range(10))
    return {"graph": "Petersen", "vertices": 10, "diameter": diam,
            "grid": f"{{0..{diam}}}^10 with sup metric", "isometric": True}


def psi_inverse_bound(samples):
    """psi(t)=t/log(e+t); the review proves psi(2u log(e+u)) >= u. Sample it."""
    worst = math.inf
    for k in range(-40, 200):
        u = math.exp(k / 4)
        t = 2 * u * math.log(math.e + u)
        worst = min(worst, (t / math.log(math.e + t)) / u)
    assert worst >= 1
    return {"samples": samples, "min_ratio_psi(2u log(e+u))/u": worst,
            "status": "floating sample only; inequality proved in review.md"}


def diagonal_type_gap(m):
    """A_j = e_j e_j^*: l2-sum of trace norms is sqrt(m); Gaussian average is m*sqrt(2/pi)."""
    return {"m": m, "l2_sum_of_trace_norms": math.sqrt(m),
            "gaussian_average_trace_norm": m * math.sqrt(2 / math.pi),
            "ratio": math.sqrt(m) * math.sqrt(2 / math.pi)}


def main():
    out = {
        "status": "PASS_EXACT_COMPARISON_DIAGNOSTICS",
        "scope": "Finite comparison diagnostics only; not proof, novelty or T117Q evidence.",
        "six_point_certificate": six_point_certificate(),
        "grid_uniform_average": grid_average(200),
        "frechet_isometry_example": petersen_frechet(),
        "psi_inverse_bound": psi_inverse_bound(240),
        "diagonal_type_gap": diagonal_type_gap(10 ** 4),
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
