"""Exact controls only. No numerical evidence is a universal source proof."""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json
L=Path(__file__).resolve().parent
# Independently integrate the public forcing by expanding (x-u)^n after u=x-t.
def b(n):return sum((Q((-1)**(n-k)*comb(n,k),1)/ (Q(n-k)+Q(3,2)) for k in range(n+1)),Q(0))
c={0:b(0),1:-b(1),12:5*b(12),13:-5*b(13)}
boundary=sum(c.values());poly={0:boundary/4}
for n,v in c.items():poly[n+1]=v*(Q(n)+Q(3,2))*(Q(n)+Q(1,2))
expected={0:Q(180640483,1764461790),1:Q(1,2),2:Q(-1),13:Q(10485760,676039),14:-Q(4194304,260015)}
assert poly==expected
signs=[]
for x,s in [(Q(7,10),1),(Q(3,4),-1),(Q(4,5),1),(Q(9,10),-1)]:
 v=sum((a*x**k for k,a in poly.items()),Q(0));assert v*s>0
 signs.append(dict(x=str(x),value=str(v),sign=s))
# Determinant-only underdetermination, not preservation of all period relations.
det=[]
for lam in [Q(1,3),Q(1,2),Q(1),Q(2),Q(3)]:
 A0,A1,C0,C1=lam,2*lam,3/lam,7/lam
 assert A0*C1-A1*C0==1
 det.append(dict(scale=str(lam),A0=str(A0),determinant='1'))
out=dict(public_curvature_coefficients={str(k):str(v) for k,v in poly.items()},public_four_signs=signs,determinant_only_controls=det,qualification='Exact formula controls and public refutation reproduction only; no proof of Matuzas Conjecture 1.1 or worldwide novelty.')
print(json.dumps(out,indent=2))
