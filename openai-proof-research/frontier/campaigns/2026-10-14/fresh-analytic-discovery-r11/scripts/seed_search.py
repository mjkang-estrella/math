#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Randomised local search for seeds A = D(beta), D in {-1,0,1}[x], maximising
L(A) - Lambda(A) for a Salem number.  EVIDENCE ONLY (double precision).

L(A) = -log(sum_r |D(z_r)|), Lambda(A) = sum_{j<=0} f(A beta^j)
                                         + sum_{j>=1} f(A' beta^{-j}).
"""
import cmath
import json
import math
import random
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from salem_numerics import Salem, f  # noqa: E402


def evaluate(S, D, tail=60):
    R = len(D) - 1
    zs = [cmath.exp(1j * t) for t in S.thetas]
    circ = [abs(sum(d * z ** l for l, d in enumerate(D))) for z in zs]
    delta = sum(circ)
    A = sum(d * S.beta ** l for l, d in enumerate(D))
    if delta == 0 or abs(A) < 1.0:
        return None  # excludes A = 0 (multiples of the minimal polynomial)
    L = -math.log(delta)
    lam = 0.0
    gtab = {n: S.g(n) for n in range(-(R + tail) - 1, R + 1)}
    for j in range(-(R + tail), 1):
        u = 0.0
        for l, d in enumerate(D):
            if d:
                u += d * gtab[l + j]
        lam += f(u)
    binv = 1.0 / S.beta
    for j in range(1, tail + 1):
        u = sum(d * binv ** (l + j) for l, d in enumerate(D) if d)
        lam += f(u)
    return L, lam, circ


def search(S, R, iters, seed):
    rng = random.Random(seed)
    D = [0] * (R + 1)
    D[0] = 1
    D[R] = -1
    best = None
    cur = evaluate(S, D)
    while cur is None:
        D[rng.randrange(1, R)] = rng.choice((-1, 1))
        cur = evaluate(S, D)
    cur_score = cur[0] - cur[1]
    temp = 2.0
    for it in range(iters):
        E = list(D)
        for _ in range(rng.choice((1, 1, 2))):
            p = rng.randrange(R + 1)
            E[p] = rng.choice((-1, 0, 1))
        if E[0] == 0 or not any(E):
            continue
        res = evaluate(S, E)
        if res is None or math.isinf(res[1]):
            continue
        sc = res[0] - res[1]
        if sc > cur_score or rng.random() < math.exp((sc - cur_score) / temp):
            D, cur, cur_score = E, res, sc
            if best is None or sc > best[0]:
                best = (sc, list(D), res)
        temp = max(0.05, temp * 0.9995)
    return best


def main():
    S = Salem([1, 0, -4, -1], "x^6-x^4-x^3-x^2+1")
    out = []
    for R in (12, 24, 40, 80):
        for seed in range(3):
            b = search(S, R, 6000, seed)
            out.append({"R": R, "seed": seed, "L_minus_Lambda": b[0],
                        "L": b[2][0], "Lambda": b[2][1],
                        "circle_abs": b[2][2], "D": b[1]})
            print(R, seed, round(b[0], 3), round(b[2][0], 3),
                  round(b[2][1], 3), file=sys.stderr)
    json.dump(out, sys.stdout, indent=1)


if __name__ == "__main__":
    main()
