#!/usr/bin/env python3
"""Finite n=2 Gaussian quadrature diagnostic; not a proof of SOUP. MIT."""
import json
import math

def check(order, beta, q, r, tau):
    # Composite trapezoidal quadrature on [-10,10] with Gaussian weights.
    step = 20/order
    grid = [-10+i*step for i in range(order+1)]
    weights = [step*math.exp(-z*z/2)/math.sqrt(2*math.pi)*(0.5 if i in (0,order) else 1) for i,z in enumerate(grid)]
    scale = 2**(-1/6)
    clock = 2**(-2/3)
    b = beta/math.sqrt(2)
    def logcosh(a):
        return abs(a)+math.log1p(math.exp(-2*abs(a)))-math.log(2)
    center = math.fsum(w*logcosh(b*z) for z,w in zip(grid,weights))
    def pair(t):
        rho = math.exp(-t*clock)
        transverse = math.sqrt(1-rho*rho)
        mass, overlap = [], []
        for x,wx in zip(grid,weights):
            for v,wv in zip(grid,weights):
                y = rho*x+transverse*v
                wt = wx*wv*math.exp(q*scale*(logcosh(b*x)-center)+r*scale*(logcosh(b*y)-center))
                mass.append(wt)
                # In n=2, <R^2>-1/2 = tanh(b*x)*tanh(b*y)/2.
                overlap.append(wt*math.tanh(b*x)*math.tanh(b*y)/2)
        m = math.fsum(mass)
        return math.log(m), -beta**2/2*q*r*rho*math.fsum(overlap)/m
    h = 1e-4
    lhs = (pair(tau-2*h)[0]-8*pair(tau-h)[0]+8*pair(tau+h)[0]-pair(tau+2*h)[0])/(12*h)
    rhs = pair(tau)[1]
    return {'mesh_intervals':order,'beta':beta,'q':q,'r':r,'tau':tau,'finite_difference':lhs,'identity_rhs':rhs,'absolute_error':abs(lhs-rhs)}

rows=[check(order,*case) for order in (160,240) for case in ((1.3,.2,.4,.7),(1.3,-.3,.4,1.1),(1.7,.1,-.2,.9))]
assert max(row['absolute_error'] for row in rows)<1e-7, rows
print(json.dumps({'purpose':'n=2 normalization/sign diagnostic, not limiting proof','passed':True,'cases':rows},indent=2))
