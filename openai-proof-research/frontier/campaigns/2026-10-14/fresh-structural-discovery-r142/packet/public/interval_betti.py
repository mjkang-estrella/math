"""Exact endpoint recursion for ambient Betti tables of box-stable ideal pairs.

Inputs A,B are standard-monomial downsets of S/I,S/J, B<=A.
This computes supporting mathematics, not the unfrozen universal lex inequality.
"""
from functools import lru_cache
from math import comb

@lru_cache(None)
def interval_betti(A, B, box):
    if not B <= A:
        raise ValueError('Expected nested standard sets')
    n = len(box)
    if n == 0:
        return {(0, 0): len(A - B)} if A != B else {}
    a = box[-1]
    As = [frozenset(u[:-1] for u in A if u[-1] == s) for s in range(a)]
    Bs = [frozenset(u[:-1] for u in B if u[-1] == s) for s in range(a)]
    out = {}
    def add(p, j, v):
        if v:
            out[p, j] = out.get((p, j), 0) + v
    for (p, j), v in interval_betti(As[0], Bs[0], box[:-1]).items():
        add(p, j, v)
    for (p, j), v in interval_betti(As[-1], Bs[-1], box[:-1]).items():
        add(p+1, j+a, v)
    for s in range(1, a):
        kernel = (As[s-1] - As[s]) - Bs[s-1]
        cokernel = (Bs[s-1] & As[s]) - Bs[s]
        for p in range(n):
            for u in cokernel:
                add(p, sum(u)+s+p, comb(n-1, p))
            for u in kernel:
                add(p+1, sum(u)+s+p, comb(n-1, p))
    return out
