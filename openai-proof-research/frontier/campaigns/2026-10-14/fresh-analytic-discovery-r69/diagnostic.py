#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Exact finite affine-coordinate algebra; not a test of the analytic theorem."""
from fractions import Fraction as Q
from itertools import product
import json
vals=[Q(-1),Q(0),Q(2,3)];times=[Q(-1,8),Q(0),Q(1,8)]
n=m=j=0
for k,b,x,y,t in product(vals,vals,vals,vals,times):
    xp=x-t;yp=y-t*(k*x+b);q=y-k*x*x/2-b*x;qp=yp-k*xp*xp/2-b*xp
    assert qp==q-k*t*t/2;n+=1
    for beta in [Q(-1,2),Q(1,3)]:
        c=k/beta;d=(b+c)/beta;q=y+c*x+d;yp=y-t*(k*x+beta*y+b)
        assert yp+c*xp+d==(1-beta*t)*q;m+=1
for xi,eta,beta,delta,r,sign in product(vals,vals,[Q(-1,2),Q(1,3)],[Q(1,16),Q(1,32)],[Q(1),Q(3,2),Q(2)],[-1,1]):
    lam=xi+beta*eta;mu=eta*beta*beta;den=1-sign*beta*delta*r
    direct=-sign*delta*xi-eta*sign*beta*delta/den
    rewritten=-sign*lam*delta-mu*delta*delta*r/den
    assert direct==rewritten;j+=1
counts=[]
for lam,mu in product([Q(0),Q(1,1000),Q(1),Q(1000)],repeat=2):
    count=0
    for k in range(40):
        d=Q(1,2**(k+1))
        if lam and mu and Q(1,8)<abs(lam)/(abs(mu)*d)<8:count+=1
    assert count<=7;counts.append(count)
print(json.dumps({'status':'PASS_FINITE_ALGEBRA_ONLY','parabolic_cases':n,'transverse_affine_cases':m,'phase_derivative_cases':j,'exceptional_scale_cases':len(counts),'largest_exceptional_count':max(counts),'full_maximal_theorem_proved':False},indent=2))
