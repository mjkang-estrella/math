"""Numerical sanity check of the weighted moment estimate (D).

For K = [-1, 1]^2 with a log-concave density f (restricted Gaussian or a
product of one-sided exponentials), random sites and intercepts, and random
intercept directions q, compute symmetric difference quotients of cell
masses M_i and first moments B_i by midpoint-rule quadrature and report

    ratio = sum |dB_i|^2 / M_i  /  (R^2 sum |dM_i|^2 / M_i)

which the proof bounds by 162 (R = sqrt(2) here). Evidence only.

Author: Myeongjin Kang. MIT License.
"""

import json
import math
import random
import sys


def make_density(rng):
    kind = rng.choice(["gauss", "exp", "tent"])
    if kind == "gauss":
        cx, cy, s = rng.uniform(-1, 1), rng.uniform(-1, 1), rng.uniform(0.3, 1.5)
        return kind, lambda x, y: math.exp(-((x - cx) ** 2 + (y - cy) ** 2) / (2 * s * s))
    if kind == "exp":
        ax, ay = rng.uniform(-4, 4), rng.uniform(-4, 4)
        return kind, lambda x, y: math.exp(ax * x + ay * y)
    # concave tent (log-concave, vanishes on the boundary of the square)
    return kind, lambda x, y: (1 - abs(x)) * (1 - abs(y))


def cells(points, weights, sites, c):
    n = len(sites)
    M = [0.0] * n
    B = [[0.0, 0.0] for _ in range(n)]
    for (x, y), w in zip(points, weights):
        best, bi = None, 0
        for i, (sx, sy) in enumerate(sites):
            v = x * sx + y * sy + c[i]
            if best is None or v > best:
                best, bi = v, i
        M[bi] += w
        B[bi][0] += w * x
        B[bi][1] += w * y
    return M, B


def main():
    rng = random.Random(16102026)
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    grid = int(sys.argv[2]) if len(sys.argv) > 2 else 220
    R2 = 2.0
    worst = 0.0
    records = []
    for _ in range(trials):
        kind, f = make_density(rng)
        hstep = 2.0 / grid
        pts = [(-1 + (i + 0.5) * hstep, -1 + (j + 0.5) * hstep)
               for i in range(grid) for j in range(grid)]
        ws = [f(x, y) for x, y in pts]
        z = sum(ws)
        ws = [w / z for w in ws]
        n = rng.randint(3, 5)
        sites = [(rng.uniform(-2, 2), rng.uniform(-2, 2)) for _ in range(n)]
        c = [rng.uniform(-0.3, 0.3) for _ in range(n)]
        M, _ = cells(pts, ws, sites, c)
        if min(M) < 0.02:
            continue
        q = [rng.uniform(-1, 1) for _ in range(n)]
        s = 0.02
        Mp, Bp = cells(pts, ws, sites, [ci + s * qi for ci, qi in zip(c, q)])
        Mm, Bm = cells(pts, ws, sites, [ci - s * qi for ci, qi in zip(c, q)])
        dM = [(a - b) / (2 * s) for a, b in zip(Mp, Mm)]
        dB = [((a[0] - b[0]) / (2 * s), (a[1] - b[1]) / (2 * s)) for a, b in zip(Bp, Bm)]
        num = sum((bx * bx + by * by) / m for (bx, by), m in zip(dB, M))
        den = R2 * sum(dm * dm / m for dm, m in zip(dM, M))
        if den < 1e-9:
            continue
        r = num / den
        worst = max(worst, r)
        records.append({"density": kind, "cells": n, "ratio": round(r, 4)})
    print(json.dumps({"check": "moment", "grid": grid, "records": records,
                      "max_ratio": worst, "bound": 162,
                      "passes": worst <= 162}))


if __name__ == "__main__":
    main()
