#!/usr/bin/env python3
"""Exact finite interface diagnostics; not an analytic or novelty certificate."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Q
import json
import itertools


def run():
    n = 0
    for M, N, R, eta, r, beta in itertools.product(
            [Q(1), Q(3, 2), Q(5)], [Q(1), Q(4)],
            [Q(1, 3), Q(1), Q(10), Q(100)],
            [Q(1, 10), Q(1), Q(2)], [Q(1, 8), Q(1), Q(3)],
            [Q(1, 5), Q(1), Q(4)]):
        c0, c1 = 2*M, 2*N*(2*M+1)
        delta = min(beta/2, r/(4*M), 1/(4*N*(2*M+1)),
                    eta/(2*(c0+c1*R))) / 2
        lip = N*(2*M+1)*delta
        assert delta < beta/2 and 2*M*delta < r
        assert lip < Q(1, 4)
        assert M*delta + lip*2*M*delta < 2*M*delta
        assert lip/(1-lip) <= c1*delta
        assert (c0+c1*R)*delta < eta/2
        n += 1
    sym = 0
    for p, q, a, g in itertools.product(range(-3, 4), range(-3, 4),
                                      [Q(1), Q(2, 3), Q(-5)],
                                      [Q(1, 2), Q(-2), Q(7)]):
        v = (a*q, -a*p)
        assert p*v[0]+q*v[1] == 0
        # omega' = g omega, coefficient a' = g a for the same
        # element of Omega_C^1 tensor L^*.
        vprime = ((g*a)*q/g, -(g*a)*p/g)
        assert v == vprime
        sym += 1
    pole = 0
    for b, w in itertools.product([Q(1, 3), Q(2), Q(-4, 5)],
                                   [Q(i, 7) for i in range(-10, 11)]):
        if 1-b*w == 0:
            continue
        derivative = ((1-b*w)+b*w)/(1-b*w)**2
        assert derivative*(1-b*w)**2 == 1
        pole += 1
    G = [[0, 2, 2], [2, 0, 2], [2, 2, 0]]
    det = (G[0][0]*(G[1][1]*G[2][2]-G[1][2]*G[2][1])
           -G[0][1]*(G[1][0]*G[2][2]-G[1][2]*G[2][0])
           +G[0][2]*(G[1][0]*G[2][1]-G[1][1]*G[2][0]))
    assert det == 16
    assert sum(sum(row) for row in G) == 12
    return {"status": "PASS", "A98_budget_cases": n,
            "relative_symplectic_twist_cases": sym,
            "moving_pole_derivative_cases": pole,
            "Wehler_pencil_Gram_determinant": det,
            "scope": "finite exact algebra only"}


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True))
