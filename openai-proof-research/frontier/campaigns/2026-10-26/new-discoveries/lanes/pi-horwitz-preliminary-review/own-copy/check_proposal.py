#!/usr/bin/env python3
"""Independent symbolic finite checks of the proposed universal argument."""
from pathlib import Path
import json
import sympy as s

t,a=s.symbols('t a',positive=True)
rows=[]
for n in range(2,13):
    m=n-1
    c=[(-1)**(j-1)*s.binomial(m,j)/j for j in range(1,m+1)]
    tay=s.log(a)+sum((-1)**(k-1)*(t/a-1)**k/s.Integer(k) for k in range(1,m+1))
    plane=s.log(a)-s.harmonic(m)+sum(c[j-1]*t**j/a**j for j in range(1,m+1))
    assert s.expand(tay-plane)==0
    assert all(s.simplify(s.diff(s.log(t)-plane,t,k).subs(t,a))==0 for k in range(m+1))
    assert s.simplify(s.diff(t**m*s.log(t),t,m)-s.factorial(m)*(s.log(t)+s.harmonic(m)))==0
    rows.append({'n':n,'Taylor_plane':'PASS','contact_through_order':m,'Rolle_derivative':'PASS'})
for n in range(2,9):
    m=n-1
    curve=[t**j for j in range(1,m+1)]+[s.log(t)]
    tangent=s.Matrix([[s.diff(f,t,r) for f in curve] for r in range(1,n)])
    # Source normal: (+W1,-W2,...), directly from derivative cofactors.
    normal=s.Matrix([(-1)**j*tangent[:,[k for k in range(n) if k!=j]].det() for j in range(n)])
    expected=s.Matrix([-(-1)**(j-1)*s.binomial(m,j)/(j*t**j) for j in range(1,m+1)]+[s.Integer(1)])
    factor=(-1)**(n+1)*s.prod(s.factorial(j) for j in range(1,n))
    assert all(s.simplify(normal[j]-factor*expected[j])==0 for j in range(n))
    nodes=list(range(1,n+1))
    A=s.Matrix([list(normal.subs(t,u)) for u in nodes])
    rhs=s.Matrix([sum(curve[j].subs(t,u)*normal[j].subs(t,u) for j in range(n)) for u in nodes])
    point=A.inv()*rhs
    identric_log=sum(s.Integer(u)**m*s.log(u)/s.prod(u-v for v in nodes if v!=u) for u in nodes)-s.harmonic(m)
    assert s.simplify(point[-1]-identric_log)==0
    rows[n-2]['literal_Wronskian_intersection']='PASS'
out={'status':'PASS: finite symbolic evidence only','checks':rows,'credit':0,'formal_endpoint':'absent'}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
