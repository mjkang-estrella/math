#!/usr/bin/env python3
"""Exact arithmetic and exhaustive shuffle checks, independent of the Lean proof."""
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]

def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0

def entry(n, i, j):
    return Q(choose(i-1, j-1)+choose(i-1, n-j), 2**i)

def vector(n):
    return [n*n-3*n*k+Q(3*k*(k+1),2)-1 for k in range(1,n+1)]

def action(m,v):
    return [sum(a*b for a,b in zip(row,v)) for row in m]

for n in range(1,81):
    m = [[entry(n,i,j) for j in range(1,n+1)] for i in range(1,n+1)]
    v = vector(n)
    assert action(m,v) == [x/4 for x in v]
    assert (any(v)) == (n >= 3)
    if n >= 3:
        assert v[0] == (n-1)*(n-2) > 0

for n in range(1,11):
    counts = [[0]*n for _ in range(n)]
    for bits in product([False,True], repeat=n):
        deck=[]
        # Draw cards n,...,1 from the bottom of the initial deck.
        for card, top in zip(range(n,0,-1),bits):
            if top: deck.insert(0,card)
            else: deck.append(card)
        for position,card in enumerate(deck):
            counts[card-1][position] += 1
    for i in range(1,n+1):
        for j in range(1,n+1):
            assert Q(counts[i-1][j-1],2**n) == entry(n,i,j)

for r in range(31):
    for a,b,c in [(1,0,0),(0,1,0),(0,0,1),(3,-7,11)]:
        lhs=sum(choose(r,k)*(a*k*k+b*k+c) for k in range(r+1))
        rhs=2**r*(Q(a*r*(r+1),4)+Q(b*r,2)+c)
        assert lhs == rhs

n=3
v=vector(n)
wrong_matrix=[[Q(choose(n-i,j-1)+choose(n-i,n-j),2**(n-i+1))
               for j in range(1,n+1)] for i in range(1,n+1)]
assert action(wrong_matrix,v) != [x/4 for x in v]
assert vector(2) == [0,0]
report={"status":"PASS", "rational_eigenidentities":"n=1..80", "nonzero":"exactly n>=3 in tested range", "exhaustive_bottom_draw_shuffles":"n=1..10, all 2^n coin assignments", "quadratic_moments":"r=0..30, four independent coefficient choices", "negative_controls":{"reversed_row_convention_n3":"rejected", "nonzero_at_n2":"rejected"}, "qualification":"Finite supplemental checks, not a replacement for the universal Lean theorem."}
(ROOT/'build/exact-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
