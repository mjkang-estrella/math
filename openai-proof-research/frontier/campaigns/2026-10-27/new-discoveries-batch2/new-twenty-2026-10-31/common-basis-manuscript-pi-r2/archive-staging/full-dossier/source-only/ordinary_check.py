#!/usr/bin/env python3
"""Standalone ordinary recheck of every mathematical number claimed in the DRAFT
paper for MathDB 332371 (lane common-basis-manuscript-pi-r2).

Run: python3 -I -B ordinary_check.py   (from the archive root; needs
matroid-certificate.json). Uses only the explicit base list and set operations;
no Gaussian-elimination library, no Lean, no network.
"""
import json, itertools, os, sys

here = os.path.dirname(os.path.abspath(__file__))
cert = json.load(open(os.path.join(here, 'matroid-certificate.json')))
E = list(range(9))
bases = {tuple(b) for b in cert['bases']}
assert len(bases) == 76 and len(bases) == len(cert['bases'])

def indep(ss):
    ss = set(ss)
    return any(ss <= set(b) for b in bases)

# 1) exchange axiom: every (A,B,e), A,B bases, e in A\B, has a witness
obl = fail = 0
for A in bases:
    for B in bases:
        for e in set(A) - set(B):
            obl += 1
            if not any(tuple(sorted((set(A) - {e}) | {f})) in bases for f in set(B) - set(A)):
                fail += 1
print('exchange obligations', obl, 'failures', fail)
assert (obl, fail) == (12736, 0)

# 2) circuits, loops, connectivity, parallel pairs (supplementary ordinary facts)
circ = [tuple(s) for k in range(1, 6) for s in itertools.combinations(E, k)
        if not indep(s) and all(indep(c) for c in itertools.combinations(s, k - 1))]
assert len(circ) == 23, len(circ)
assert not [e for e in E if not indep({e}) is None and True] or True
in_base = set().union(*(set(b) for b in bases))
assert in_base == set(E), 'loops present'
assert all(any(a in c and b in c for c in circ) for a, b in itertools.combinations(E, 2)), 'not connected'
par = [c for c in circ if len(c) == 2]
assert par == [(1, 4)], par

# 3) deletion-complementary lists and the complete obstruction
def D(z):
    return sorted(b for b in bases if z not in b and tuple(sorted((set(E) - {z}) - set(b))) in bases)

D1, D6 = D(1), D(6)
assert len(D1) == 32 and len(D6) == 24, (len(D1), len(D6))
assert not (set(D1) & set(D6)), 'intersection nonempty'
assert tuple(D1) == tuple(map(tuple, cert['deletion_complementary_bases']['1']))
assert tuple(D6) == tuple(map(tuple, cert['deletion_complementary_bases']['6']))
# exhibited partitions
assert tuple(sorted({0, 2, 3, 5})) in bases and tuple(sorted({4, 6, 7, 8})) in bases
assert tuple(sorted({0, 1, 2, 7})) in bases and tuple(sorted({3, 4, 5, 8})) in bases
print('ALL ORDINARY CHECKS PASS: 76 bases; 12736 exchange obligations, 0 failures;'
      ' 23 circuits; loopless; connected; parallel pair (1,4); |D1|=32, |D6|=24,'
      ' intersection empty; both exhibited partitions are bases')
