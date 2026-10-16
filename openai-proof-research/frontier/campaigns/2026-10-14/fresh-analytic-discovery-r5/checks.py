#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT license.
"""Support checks for explicitly stated flat models; NOT a checker of target B."""
from fractions import Fraction as F
import json
import math


def integral(coefficients, q):
    return sum((a*q**(k+1)/F(k+1) for k,a in enumerate(coefficients)),F(0))


def closed_variation(q):
    s=math.sqrt(1-q*q)
    return 8/math.pi*((q*s+math.asin(q))/2-(1-s**3)/(3*q))


def quadrature_variation(q, panels=4096):
    # Independent formula: 2* convolution of the disk marginal and triangle at 0.
    h=q/panels
    def v(z):
        return 8/math.pi*math.sqrt(1-z*z)*(1-z/q)
    return h/3*(v(0)+v(q)+4*sum(v(k*h) for k in range(1,panels,2))
                +2*sum(v(k*h) for k in range(2,panels,2)))


def main():
    identities=[]
    for den in range(2,65):
        q=F(1,den)
        # Integral of 1-z/q and its product with 1-z^2 on [0,q].
        upper=8*integral([F(1),-1/q],q)
        lower=8*integral([F(1),-1/q,F(-1),1/q],q)
        assert upper==4*q
        assert lower==4*q-F(2,3)*q**3
        # These are pi times the variation bounds. The universal bounds are
        # proved in candidate.md from sqrt(1-z^2), not inferred from this grid.
        assert 0<lower<=upper
        identities.append(str(q))
    numerical=[]
    for q in [F(1,2),F(1,3),F(1,4),F(1,8),F(1,16)]:
        x=float(q); a=closed_variation(x); b=quadrature_variation(x)
        assert abs(a-b)<2e-12
        lo=float(4*q-F(2,3)*q**3)/math.pi
        hi=float(4*q)/math.pi
        assert lo<=a+2e-14 and a<=hi+2e-14
        numerical.append({'q':str(q),'closed':f'{a:.10f}',
                          'quadrature':f'{b:.10f}',
                          'error_bound_checked':'2e-12'})
    steps=[]
    for a,b in [(F(0),F(1)),(F(1,3),F(7,5)),(F(2),F(5))]:
        mass=b-a; continuous=mass/2; jump=mass/2
        assert continuous+jump==mass
        for c in [a,(a+b)/2,b]:
            # For the increasing step envelope clipped from below by c,
            # variation is end-trace difference, not a numerical differentiation.
            assert max(b,c)-max(a,c)==b-c
        steps.append({'a':str(a),'b':str(b),'continuous':str(continuous),
                      'jump':str(jump),'total':str(mass)})
    # An exact accounting obstruction to replacing strict by measure-norm
    # convergence: the derivative of an n-step ramp is atomic, and hence
    # mutually singular with Lebesgue measure on the unit interval.
    staircase=[]
    for n in [2,3,7,31,127]:
        atomic_mass=sum((F(1,n) for _ in range(n)),F(0))
        assert atomic_mass==1
        norm_difference=atomic_mass+F(1)
        assert norm_difference==2
        staircase.append({'n':n,'input_variation':str(atomic_mass),
                          'derivative_measure_norm_difference':str(norm_difference)})
    return {'scope':'flat layer support only; no proof or disproof of B',
            'rational_bound_identity_count':len(identities),
            'closed_form_comparisons':numerical,'step_accounting':steps,
            'strict_vs_strong_obstruction':staircase,
            'universal_numerical_claim':False,'independent_review':False}


if __name__=='__main__':
    print(json.dumps(main(),indent=2,sort_keys=True))
