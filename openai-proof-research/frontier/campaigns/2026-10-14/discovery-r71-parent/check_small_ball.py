#!/usr/bin/env python3
"""MIT. Exact finite arithmetic checks, not the uniform probabilistic proof."""
from fractions import Fraction as F
from itertools import product
from math import comb
import json

count = 0
for p, k, n in product([F(1,10), F(1,4), F(2,5), F(3,5), F(9,10)], range(1,5), [1,2,5,20,1000]):
    mu = 2*p-1
    s = 1 if mu > 0 else -1
    v, u = max(p,1-p), min(p,1-p)
    coefficient = -F(s,1)/(mu*n)
    c2 = 1+1/(mu*mu*n)
    assert 1+n*coefficient**2 == c2
    assert coefficient*n*mu == -s
    assert n*coefficient**2*(1-mu*mu) == (1-mu*mu)/(mu*mu*n)
    assert v**k-p**(k+1)-(1-p)**(k+1) == u*(v**k-u**k) > 0
    count += 4

# Exact one-dimensional probabilities; independent disjoint blocks give a
# sup-norm event contained in the Euclidean ball of radius sqrt(k)*r.
enumerations = []
for p, n, r in product([F(1,10), F(1,4), F(3,5)], [2,5,10,20], [F(1,4),F(1,2)]):
    mu = 2*p-1
    s = 1 if mu > 0 else -1
    c2 = 1+1/(mu*mu*n)
    mass = F(0)
    conditional = F(0)
    for plus in range(n+1):
        eta_sum = 2*plus-n
        weight = comb(n,plus)*p**plus*(1-p)**(n-plus)
        tail = -F(s,1)*eta_sum/(mu*n)
        if (s+tail)**2 <= c2*r*r:
            conditional += weight
        for sign,prob in [(1,p),(-1,1-p)]:
            if (sign+tail)**2 <= c2*r*r:
                mass += prob*weight
    variance = (1-mu*mu)/(mu*mu*n)
    v = max(p,1-p)
    assert conditional >= 1-variance/(c2*r*r)
    assert mass >= v*(1-variance/(c2*r*r))
    enumerations.append(dict(p=str(p),n=n,r=str(r),mass=str(mass)))

# Concrete dimension where the lower bound already beats f(3).
p, k, n, r = F(1,10), 2, 1000, F(1,4)
mu = 2*p-1
c2 = 1+1/(mu*mu*n)
lower = (1-p)**k*(1-k*(1-mu*mu)/(mu*mu*n*c2*r*r))
assert lower > p**(k+1)+(1-p)**(k+1)
print(json.dumps(dict(status='PASS_FINITE_ARITHMETIC_ONLY',identity_checks=count,
    exact_binomial_cases=len(enumerations),concrete_lower_bound=str(lower),
    exact_atom_bound=str(p**3+(1-p)**3),limits='Not a proof substitute or matrix-conjecture solution'),indent=2))
