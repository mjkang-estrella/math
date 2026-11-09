#!/usr/bin/env python3
"""Supplementary exact symbolic identities and numerical source checks, not proof inputs."""
import json
from pathlib import Path
import sympy as s
import mpmath as mp

z,a,t=s.symbols('z a t')
U=lambda q:1/(12*q)-1/(360*q**3)+1/(1260*q**5)
N,D=s.factor(1/(12*(z+a)-s.Rational(1,4))-U(z)+a*a/(2*z+a)).as_numer_denom()
A,B,C,E=s.Poly(N,a).all_coeffs()
delta=s.expand(4*B*E-C*C)
assert all(v>0 for v in s.Poly(B.subs(z,t+1),t).all_coeffs())
assert all(v>0 for v in s.Poly(delta.subs(z,t+1),t).all_coeffs())
v=1/(2*z+1)
b=v*v/3+v**4/5+v**6/7+v**8/(1-v*v)
n,d=s.factor(U(z)-U(z+1)-b).as_numer_denom()
assert all(x>0 for x in s.Poly(n,z).all_coeffs())
mp.mp.dps=60
worst=None
count=0
for x in [mp.mpf(i)/100 for i in range(101)]+[mp.mpf(2),10,100]:
    for al in [mp.mpf(i)/100 for i in range(101)]+[mp.mpf(2),10,100]:
        q=x+al+mp.mpf('.5')
        e=mp.loggamma(x+1)+al*mp.log(x+1)-mp.log(2*mp.pi)/2-q*mp.log(q)+q
        target=1/(12*(x+al)+18-12*mp.exp(mp.mpf(1)/48))
        gap=target-e
        assert gap>0
        count+=1
        if worst is None or gap<worst[0]:worst=(gap,x,al)
result={'status':'Symbolic exact identities PASS; numerical evidence only for Gamma endpoint',
        'samples':count,'minimum_grid_gap':[str(y) for y in worst],
        'B_shift_ascending':[str(c) for c in reversed(s.Poly(B.subs(z,t+1),t).all_coeffs())],
        'discriminant_shift_ascending':[str(c) for c in reversed(s.Poly(delta.subs(z,t+1),t).all_coeffs())],
        'step_numerator':str(n),'step_denominator':str(d),'count_credit':0}
Path(__file__).with_name('independent-math-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'samples':count,'minimum_grid_gap':result['minimum_grid_gap']}))
