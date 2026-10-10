#!/usr/bin/env python3
"""Exact finite budget diagnostics; no mathematical theorem certification."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
import json

def main():
    count = 0
    for M in (1, 2, 7):
        for N in (1, 3, 11):
            for R in (F(1, 10), F(1), F(13), F(100)):
                for eta in (F(1, 20), F(1), F(5)):
                    r, beta = F(1, 3), F(1, 5)
                    c0, c1 = 2*M, 2*N*(2*M+1)
                    delta = min(beta/2, r/(4*M), F(1, 4*N*(2*M+1)),
                                eta/(2*(c0+c1*R)))/2
                    assert 2*M*delta < r/2
                    k = N*(2*M+1)*delta
                    assert k < F(1, 4)
                    assert M*delta+k*2*M*delta < 2*M*delta
                    assert k/(1-k) <= c1*delta
                    assert R+(c0+c1*R)*delta < R+eta/2
                    count += 1
    recurrences = 0
    for Q in (6, 7, 9):
        D, theta = F(32), F(1, 2)
        e = theta/(D*2**Q)
        for n in range(9):
            x = D*2**(Q*(n+1))*e
            assert x == theta**(2**n)
            next_e = D*2**(Q*n)*e*e
            assert D*2**(Q*(n+2))*next_e == x*x
            e = next_e
            recurrences += 1
    budget = 0
    a0, ai, eps = F(3), F(1), F(1, 100)
    for n in range(20):
        an = ai+(a0-ai)/2**n
        an1 = ai+(a0-ai)/2**(n+1)
        assert an-an1 == (a0-ai)/2**(n+1)
        assert sum(eps/2**(j+1) for j in range(n+1)) == eps*(1-F(1,2**(n+1)))
        budget += 1
    # For a chosen germ w/(1-bw), the kth b coefficient is w^(k+1).
    # This is a finite formal identity, not an analytic nonextension proof.
    pole = 0
    for w in (F(1, 2), F(2), F(7)):
        for b in (F(1, 100), F(1, 50)):
            for n in range(1, 10):
                partial = sum(b**k*w**(k+1) for k in range(n))
                assert partial*(1-b*w) == w-b**n*w**(n+1)
                pole += 1
    print(json.dumps({'status':'PASS','A98_budget_cases':count,
        'S102_Newton_rescalings':recurrences,'E102_budget_cases':budget,
        'G102_pole_jet_identities':pole,
        'scope':'finite exact arithmetic only; no family construction or analytic proof certification'},indent=2))

if __name__ == '__main__':
    main()
