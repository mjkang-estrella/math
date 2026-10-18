#!/usr/bin/env python3
# Copyright (c) Myeongjin Kang. SPDX-License-Identifier: MIT
"""Exact finite algebra checks; not a proof of either research target."""
import json
import sympy as s
count = 0
for n in (2,3):
    z=s.symbols('z:'+str(n)); w=s.symbols('w:'+str(n))
    q=sum(z[i]*w[i] for i in range(n))
    for a in range(3):
        for b in range(3):
            P=z[0]**a*w[1]**b
            for k in range(4):
                u=q**k*P
                lap=sum(s.diff(u,z[i],w[i]) for i in range(n))
                radial=sum(z[i]*w[j]*s.diff(u,z[i],w[j]) for i in range(n) for j in range(n))
                expected_lap=0 if k==0 else k*(k+n+a+b-1)*q**(k-1)*P
                expected_radial=(k+a)*(k+b)*q**k*P
                assert s.expand(lap-expected_lap)==0
                assert s.expand(radial-expected_radial)==0
                count+=1
# Fundamental-theorem-of-calculus identity for arbitrary degree-six polynomial.
t=s.symbols('t'); c=s.symbols('c:7'); p=sum(c[i]*t**i for i in range(7))
assert s.expand(s.integrate(t*s.diff(p,t,2),(t,0,1))-(p.subs(t,0)-p.subs(t,1)+s.diff(p,t).subs(t,1)))==0
# Balancing exponential truncation and amplified residual.
a,C,L=s.symbols('a C L',positive=True); N=L/(a+C)
assert s.simplify((-L+C*N)-(-a*N))==0
print(json.dumps({'status':'PASS','angular_polynomial_cases':count,'pressure_polynomial_identity':True,'error_balance_identity':True,'research_targets_proved':False},sort_keys=True))
