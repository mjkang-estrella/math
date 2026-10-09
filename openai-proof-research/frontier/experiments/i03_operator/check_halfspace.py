#!/usr/bin/env python3
"""Exact transcription checks, not proofs of any infinite-dimensional assertion.
No finite replacement for the actual normalizer L is made.
Run from any directory; output is written next to this script.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json


def exponent(j, x):
    k = j if j >= 0 else -j - 1
    if k == 0:
        return 10
    m = 1
    while k >= 8**m:
        m += 1
    n = 2**m
    residue = x % n
    return 10*(k+1) + 100*(n-2) + 100*(residue if j >= 0 else n-1-residue)


def log_weights(x, n):
    w = {0: 0}
    for j in range(n):
        w[j+1] = w[j] - exponent(j, x)
    for j in range(-1, -n-1, -1):
        w[j] = w[j+1] + exponent(j, x)
    return w


def log_unnormalized_b(x, n):
    b = {0: 0}
    for j in range(n):
        b[j+1] = b[j] + exponent(j, x) - exponent(j-1, x+1)
    for j in range(-1, -n-1, -1):
        b[j] = b[j+1] - exponent(j, x) + exponent(j-1, x+1)
    return b

checks = 0
for x in range(64):
    w = log_weights(x, 602)
    wp = log_weights(x+1, 602)
    b = log_unnormalized_b(x, 601)
    for j in range(-600, 601):
        assert b[j] + w[j] - wp[j-1] == -10
        checks += 1

I = ((F(1), F(0)), (F(0), F(1)))
Z = (F(0), F(0))
C = ((F(1,5), F(2,5)), (F(0), F(3,5)))

def mm(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))

def mv(a, v):
    return tuple(sum(a[i][j]*v[j] for j in range(2)) for i in range(2))

def add(u, v):
    return tuple(a+b for a,b in zip(u,v))

def scale(a, v):
    return tuple(a*x for x in v)

def power(a, n):
    r = I
    for _ in range(n):
        r = mm(r, a)
    return r

def W(j):
    return ((F(1), F(j)), (F(j), F(1+j*j)))

def Wi(j):
    return ((F(1+j*j), F(-j)), (F(-j), F(1)))

# Forward block from j to j+1 and backward block from j to j-1.
def A(j):
    return mm(W(j+1), Wi(j))

def D(j):
    return mm(mm(W(j-1), C), Wi(j))

assert mm(W(2), C) != mm(C, W(2))
for j in range(-10, 11):
    assert mm(W(j), Wi(j)) == I
    assert mm(A(j-1), D(j)) == mm(D(j+1), A(j))

stencil_checks = 0
for sign in (1, -1):
    for radius in range(1, 8):
        h = {0: (F(2), F(3)) if sign == 1 else Z}
        for j in range(1, radius+1):
            h[j] = (F(j+1), F(j*j-2))
            h[-j] = scale(sign, mv(power(C, j), h[j]))
        f = {j: mv(W(j), v) for j,v in h.items()}
        result = {}
        # Include BOTH newly reached outer coordinates, never truncate the output.
        for j in range(-radius-1, radius+2):
            result[j] = add(mv(A(j-1), f.get(j-1, Z)), mv(D(j+1), f.get(j+1, Z)))
        k = {j: mv(Wi(j), v) for j,v in result.items()}
        for j in range(1, radius+2):
            assert k[-j] == scale(sign, mv(power(C,j), k[j]))
            stencil_checks += 1
        if sign == -1:
            assert k[0] == Z

# Exact Laurent/binomial formula for a central-coordinate input.
g = (F(3), F(-2))
orbit = {0:g}
for n in range(11):
    expected = {n-2*l: scale(comb(n,l), mv(power(C,l), g)) for l in range(n+1)}
    assert orbit == expected
    orbit = {j: add(orbit.get(j-1,Z), mv(C,orbit.get(j+1,Z))) for j in range(-n-1,n+2,2)}

output = {
    'status': 'pass',
    'integer_log_identity_checks': checks,
    'residues': [0,63],
    'indices': [-600,600],
    'rational_reflection_relations_checked': stencil_checks,
    'rational_commutation_blocks_checked': 21,
    'central_binomial_orbits_checked': 11,
    'normalizer_L_approximated': False,
    'scope': 'Finite exact transcription checks only. Closure, invariance and half-space claims require the report proofs.'
}
Path(__file__).with_name('output.json').write_text(json.dumps(output, indent=2)+'\n')
print(json.dumps(output, indent=2))
