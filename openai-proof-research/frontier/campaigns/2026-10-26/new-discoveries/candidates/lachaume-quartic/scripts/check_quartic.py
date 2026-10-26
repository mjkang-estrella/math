#!/usr/bin/env python3
"""Exact rational checks; these supplement the proposed proof, not Lean."""
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

def add(p,q):
    return [(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))]
def mul(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return out
def scale(a,p):return [a*v for v in p]
def deriv(p):return [i*p[i] for i in range(1,len(p))]
def ev(p,x):return sum(a*x**i for i,a in enumerate(p))
P=list(map(F,[1,8,6,8,1]));Pd=deriv(P);Pdd=deriv(Pd)
Q=add(scale(4,mul(P,Pdd)),scale(-3,mul(Pd,Pd)))
assert Q==list(map(F,[-144,0,288,0,-144,0,0]))
# Direct literal elementary-symmetric sum, all six pair and all four triple terms.
def f(v):
    a=[1,2,1,2,1]
    return sum(a[k]*sum(product(v[i] for i in I) for I in combinations(range(4),k)) for k in range(5))
def product(xs):
    out=F(1)
    for x in xs:out*=x
    return out
g=[F(5),F(12),F(15),F(4)]
points=[F(1,20),F(1,10),F(3,20)]
expected=[F(2819,500),F(3177,500),F(7151,1000)]
for t,y in zip(points,expected):assert f([F(2),t,t,t])==ev(g,t)==y
for t in [F(1,100),F(1,10),F(1),F(2),F(10)]:assert f([t]*4)==ev(P,t)
# Fourth-root bounds: lower left, upper middle, lower right.
L=F(15409,10000);U=F(15877,10000);R=F(16352,10000)
assert L>0 and U>0 and R>0
assert L**4<expected[0] and expected[1]<U**4 and R**4<expected[2]
assert U<(L+R)/2
C=add(scale(4,mul(g,deriv(deriv(g)))),scale(-3,mul(deriv(g),deriv(g))))
result={'status':'PASS','quartic_coefficients_ascending':list(map(str,P)),
'normalized_Laguerre_coefficients_ascending':list(map(str,Q)),
'Jensen_points':[str(t) for t in points], 'literal_f_values':list(map(str,expected)),
'fourth_root_bounds':{'left_lower':str(L),'middle_upper':str(U),'right_lower':str(R),'strict_rational_gap':str((L+R)/2-U)},
'off_diagonal_normalized_curvature_coefficients_ascending':list(map(str,C)),
'qualification':'Exact supporting computations only; formal proof and bounded novelty review pending; credit0.'}
Path(__file__).with_name('exact-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
