#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Diagnostic for B8C (evidence only, not a proof input).

Checks, in floating point, the finite identities used by candidate.md:
SIC overlaps, hole overlaps, the hole-SIC incidence, the kappa values of
the covariant perturbation, and samples the max-overlap function M_eps.
Pure standard library; writes nothing; deterministic seed.
"""
import cmath
import math
import random
import sys

W = cmath.exp(2j * math.pi / 3)
R2 = math.sqrt(2.0)
R3 = math.sqrt(3.0)


def ip(a, b):  # <a,b> = a^* b
    return sum(x.conjugate() * y for x, y in zip(a, b))


def n2(a):
    return ip(a, a).real


def X(v):
    return [v[2], v[0], v[1]]  # (Xv)(j) = v(j-1)


def Z(v):
    return [v[j] * W ** j for j in range(3)]


def orbit(f):
    out = []
    for a in range(3):
        for b in range(3):
            v = list(f)
            for _ in range(b):
                v = Z(v)
            for _ in range(a):
                v = X(v)
            out.append(v)
    return out


s0 = [0j, 1 / R2 + 0j, -1 / R2 + 0j]
d0 = [0j, (1 + 1j) / 2, (1 + 1j) / 2]
SIC = orbit(s0)
D = orbit(d0)  # d_k = W_k d0, attached to s_k = W_k s0

E = [[1 + 0j if i == j else 0j for i in range(3)] for j in range(3)]
V = {c: [[W ** ((c * j * j + a * j) % 3) / R3 for j in range(3)] for a in range(3)] for c in range(3)}
bases = [("std", E)] + [("B%d" % c, V[c]) for c in range(3)]
HOLES = [v for _, B in bases for v in B]

tol = 1e-12
ok = True

# SIC overlaps
for i in range(9):
    for j in range(9):
        o = abs(ip(SIC[i], SIC[j])) ** 2
        want = 1.0 if i == j else 0.25
        if abs(o - want) > tol:
            ok = False
            print("SIC overlap fail", i, j, o)

# hole overlaps
for h in HOLES:
    ov = sorted(abs(ip(s, h)) ** 2 for s in SIC)
    if not (all(abs(x) < tol for x in ov[:3]) and all(abs(x - 0.5) < tol for x in ov[3:])):
        ok = False
        print("hole overlap fail", ov)

# kappa on favored pairs: line b_a^perp favors b_{a+1}
kappas = []
for name, B in bases:
    for a in range(3):
        prev, fav = B[a], B[(a + 1) % 3]
        trio = [k for k in range(9) if abs(ip(prev, SIC[k])) < 1e-9]
        if len(trio) != 3:
            ok = False
            print("trio size fail", name, a)
        for k in trio:
            if abs(abs(ip(fav, SIC[k])) ** 2 - 0.5) > tol:
                ok = False
            kap = (ip(D[k], fav) * ip(fav, SIC[k])).real
            kappas.append(kap)
            # perp of d to s
            if abs(ip(SIC[k], D[k])) > tol or abs(n2(D[k]) - 1) > tol:
                ok = False
kmin = min(kappas)
print("kappa values:", sorted(set(round(k, 12) for k in kappas)))
print("kappa_min = %.12f ; 1/sqrt(24) = %.12f" % (kmin, 1 / math.sqrt(24)))
if abs(kmin - 1 / math.sqrt(24)) > 1e-12:
    ok = False


def config(eps):
    f = [(x + eps * y) / math.sqrt(1 + eps * eps) for x, y in zip(s0, d0)]
    return orbit(f)


def M(cfg, u):
    nu = n2(u)
    return max(abs(ip(s, u)) ** 2 for s in cfg) / nu


def rand_unit(rng):
    v = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(3)]
    n = math.sqrt(n2(v))
    return [x / n for x in v]


def local_min(cfg, u, rng, steps=400, scale=0.05):
    best = M(cfg, u)
    for t in range(steps):
        sc = scale * (1 - t / steps) + 1e-5
        v = [x + complex(rng.gauss(0, sc), rng.gauss(0, sc)) for x in u]
        m = M(cfg, v)
        if m < best:
            best, u = m, v
    return best, u


rng = random.Random(20261016)
for eps in (0.0, 0.01, 0.02, 0.05):
    cfg = config(eps)
    starts = [rand_unit(rng) for _ in range(20000)]
    vals = sorted(((M(cfg, u), i) for i, u in enumerate(starts)))
    mins = []
    for _, i in vals[:40]:
        mins.append(local_min(cfg, starts[i], rng)[0])
    # also start at every hole
    for h in HOLES:
        mins.append(local_min(cfg, list(h), rng, scale=0.01)[0])
    print("eps=%.3f  sampled min M = %.6f  (min M - 1/2 = %.3e)" % (eps, min(mins), min(mins) - 0.5))
    if eps > 0 and min(mins) <= 0.5:
        ok = False

print("DIAGNOSTIC", "CONSISTENT" if ok else "INCONSISTENT")
sys.exit(0 if ok else 1)
