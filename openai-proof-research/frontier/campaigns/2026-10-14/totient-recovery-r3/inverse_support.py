#!/usr/bin/env python3
"""Exact finite inverse-totient support search. Not an unboundedness proof.
Original code MIT. Requires sympy. All primality inputs here below 2**64.
"""
from functools import lru_cache
from math import prod, gcd
from fractions import Fraction
import json
from pathlib import Path
from sympy import divisors, isprime, totient, primerange

@lru_cache(None)
def candidates(d):
    return tuple(int(v)+1 for v in divisors(d) if isprime(int(v)+1))

@lru_cache(None)
def inverse(d, bound):
    # Every nonempty preimage has a unique largest prime p<bound.
    result = {1} if d == 1 else set()
    for p in candidates(d):
        if p >= bound:
            continue
        cost, power = p - 1, p
        while d % cost == 0:
            for u in inverse(d // cost, p):
                result.add(power * u)
            cost *= p
            power *= p
    return tuple(sorted(result))

def fiber(d):
    return inverse(d, d + 2)

def row(d, include_fiber=True):
    f=fiber(d)
    if not f:return None
    ratio=Fraction(f[0],d)
    return dict(d=d, least=f[0], ratio=str(ratio), count=len(f),
                common_divisor=gcd(*f), **({'fiber':list(f)} if include_fiber else {}))

if __name__=='__main__':
    # Independent direct phi table verifies completeness on a range: any
    # omitted inverse cannot exceed 2*d*d, by phi(n)>=sqrt(n/2).
    # The elementary bound is proved in checkpoint.md.
    lim=150
    brute={d:[] for d in range(1,lim+1)}
    for n in range(1,2*lim*lim+1):
        d=int(totient(n))
        if d<=lim:brute[d].append(n)
    for d in range(1,lim+1):assert list(fiber(d))==brute[d],d
    vals={2**a*3**b*5**c for a in range(1,9) for b in range(5) for c in range(3)}
    # Source witnesses and powers of primorial totients.
    vals.update([2**18*257,54,12500,294,110])
    ps=list(primerange(2,18))
    for k in range(2,len(ps)+1):
        for e in range(1,3):vals.add(int(totient(prod(ps[:k])**e)))
    rows=[r for d in sorted(vals) if (r:=row(d))]
    # Store finite maxima and examples, never extrapolate.
    top=sorted(rows,key=lambda r:Fraction(r['ratio']),reverse=True)[:20]
    out=dict(validation=dict(phi_bound='n <= 2*d^2',d_max=lim,n_max=2*lim*lim,passed=True),
             searched=len(vals),totients=len(rows),top=top,
             source_examples=[row(d) for d in [2**18*257,54,12500,294,110]],
             primorial_powers=[row(int(totient(prod(ps[:k])**e)),False) for k in range(2,len(ps)+1) for e in range(1,3)])
    Path(__file__).with_name('experiment.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k in ['validation','searched','totients']}))
    print('top',[(r['d'],r['least'],r['ratio']) for r in top[:5]])
