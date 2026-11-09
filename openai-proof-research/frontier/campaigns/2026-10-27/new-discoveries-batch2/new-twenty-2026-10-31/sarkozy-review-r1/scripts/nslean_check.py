#!/usr/bin/env python3
"""Reviewer's own rebuild of the public ns-lean q = 3, n = 8 set (810 polynomials) from the
description in ns-lean PROOF.md (commit 035e9b0c). No upstream code is used."""
import itertools
p = 3
def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return out
def add(a, b):
    n = max(len(a), len(b)); a = a + [0] * (n - len(a)); b = b + [0] * (n - len(b))
    return [(x + y) % p for x, y in zip(a, b)]
def vec(a, n):
    a = a + [0] * n
    assert all(c == 0 for c in a[n:]), "degree overflow"
    return tuple(a[:n])
code = ["0000", "0211", "0121", "0112", "1200", "1020", "1002", "2212", "2122", "2221"]
code = [tuple(int(c) for c in w) for w in code]
sq = {0, 1}
ok = all(a == b or not all(((x - y) % 3) in sq for x, y in zip(a, b)) for a in code for b in code)
print("code property (no difference with all coordinates in {0,1}):", ok, "size", len(code))
P = [0, 2, 0, 1]          # T^3 - T
Q = mul(P, P)
print("Q =", Q, "(expect T^6 + T^4 + T^2)")
A = set()
for s in code:
    s0, s1, s2, sinf = s
    V = [s0 % 3, (s2 - s1) % 3, (-(s0 + s1 + s2)) % 3]
    for r in itertools.product(range(3), repeat=3):
        for u in range(3):
            tail = [sinf, u]        # m = 0, B = {0}: b + s_inf T^0 + u T^1
            f = add(add(V, mul(P, list(r))), mul(Q, tail))
            v = vec(f, 8)
            # signature check: values at 0,1,2 equal s0,s1,s2
            for c, sc in zip(range(3), (s0, s1, s2)):
                assert sum(coef * pow(c, i, 3) for i, coef in enumerate(v)) % 3 == sc
            A.add(v)
print("|A| =", len(A), " vs 3^6 =", 3 ** 6)
sqs = set()
for b in itertools.product(range(3), repeat=8):
    if any(b):
        s = mul(list(b), list(b))
        if all(c == 0 for c in s[8:]):
            sqs.add(tuple(s[:8]))
print("distinct nonzero squares of degree < 8:", len(sqs))
viol = sum(1 for f in A for d in sqs if tuple((x + y) % 3 for x, y in zip(f, d)) in A)
print("violations f + z^2 in A:", viol)
print("RESULT nslean n=8:", "CONFIRMED 810 > 729" if viol == 0 and len(A) == 810 else "FAIL")
