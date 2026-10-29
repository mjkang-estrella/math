from pathlib import Path
from fractions import Fraction
from math import comb
import json,sympy as sp
P=Path(__file__).resolve().parent
exec((P/'check.py').read_text().split('first=None')[0])
d=json.loads((P/'route-results.json').read_text());z=d['arbitrary_positive_mixture_counterexample'];a=list(map(int,z['a']));b=list(map(int,z['b']));w=Fraction(z['weight']);i=z['index'];v=[Fraction(x)+w*y for x,y in zip(a,b)];assert v[i]**2-v[i-1]*v[i+1]==Fraction(z['defect'])<0
x=sp.Symbol('m');assert all(t>=0 for t in defects(list(map(int,d['source_row_real_rootedness_failure']['coefficients']))))
f=2*x*(x+1)*(x+2)*(x+3)*(x+4)*(11*x*x+16*x+15);assert sp.discriminant(11*x*x+16*x+15,x)==-404
assert list(reversed(sp.Poly(f,x).all_coeffs()))==list(map(int,d['source_row_real_rootedness_failure']['coefficients']))
# Polynomial recurrence D_n=n![z^n](1-z)^(-m)(1-tz)^(-m).
def shift(a):return [0]+a[:-1]
def scale_linear(a,c,d):return [c*a[i]+(d*a[i-1] if i else 0) for i in range(len(a))]
rows={}
checks=0
for n in range(41):
 rows[n]=[mul(rise[n-j],rise[j])+[0]*(40-n) for j in range(n+1)]
 rows[n]=[[comb(n,j)*c for c in a] for j,a in enumerate(rows[n])]
 if n<2:continue
 zero=[0]*41
 for j in range(n+1):
  A=rows[n-1][j] if j<n else zero;B=rows[n-1][j-1] if j>0 else zero;C=rows[n-2][j-1] if 0<j<n else zero
  rhs=[u+v-w for u,v,w in zip(scale_linear(A,n-1,1),scale_linear(B,n-1,1),scale_linear(C,(n-1)*(n-2),2*(n-1)))]
  assert rows[n][j]==rhs;checks+=1
# Independent exact check of the PUBLIC Theorem5.3; excluded, no credit.
q=[163,1790,10323,39217,106659,215169,323646,350404,232662,71162]
weighted=[comb(9,i)*c for i,c in enumerate(q)];g=sp.Poly.from_list(list(reversed(weighted)),x);real=int(sum(e*h.count_roots(-sp.oo,sp.oo) for h,e in g.sqf_list()[1]));assert real<9
out=dict(rational_mixture_defect_verified=True,actual_n7_k2_quadratic_discriminant=-404,source_row_LC=True,recurrence_integer_coefficient_identities=checks,public_successor_degree=9,public_successor_real_roots=real,public_successor_credit=0)
(P/'verification.json').write_text(json.dumps(out,indent=2));print(out)
