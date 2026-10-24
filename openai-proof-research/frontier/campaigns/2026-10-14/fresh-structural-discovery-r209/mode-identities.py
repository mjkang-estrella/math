"""Exact finite Fourier check of author torus mode identities; not a theorem verifier."""
from fractions import Fraction as F
from collections import defaultdict
import json
# Gaussian rationals as (real, imaginary), Fourier frequencies as integer pairs.
def ca(a,b):return (a[0]+b[0],a[1]+b[1])
def cm(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(a,c):return {k:(v[0]*c,v[1]*c) for k,v in a.items() if v!=(0,0)}
def add(*items):
 out={}
 for a in items:
  for k,v in a.items():out[k]=ca(out.get(k,(F(0),F(0))),v)
 return {k:v for k,v in out.items() if v!=(0,0)}
def deriv(a,j):return {k:cm(v,(F(0),F(k[j]))) for k,v in a.items() if k[j]}
def mul(a,b):
 out={}
 for k,v in a.items():
  for l,w in b.items():
   q=(k[0]+l[0],k[1]+l[1]);out[q]=ca(out.get(q,(F(0),F(0))),cm(v,w))
 return {k:v for k,v in out.items() if v!=(0,0)}
def dx(v):
 n1,e1,n2,e2=v
 return [add(deriv(n1,0),scale(e1,-1)),add(deriv(e1,0),n1),deriv(n2,0),deriv(e2,0)]
def dy(v):
 n1,e1,n2,e2=v
 return [deriv(n1,1),deriv(e1,1),add(deriv(n2,1),scale(e2,-1)),add(deriv(e2,1),n2)]
def dot(v,w):return add(*(mul(a,b) for a,b in zip(v,w)))
def avg(a):return a.get((0,0),(F(0),F(0)))
def mode(p,q):
 phi={(p,q):(F(1,2),F(0)),(-p,-q):(F(1,2),F(0))}
 return [scale(deriv(deriv(phi,0),0),-1),deriv(phi,0),deriv(deriv(phi,1),1),scale(deriv(phi,1),-1)]
v=mode(2,1);w=mode(2,-1)
rows=[]
for name,a in [('plus',v),('minus',w)]:
 ax,ay=dx(a),dy(a)
 linear=[scale(ax[1],2),add(ay[1],ax[3]),scale(ay[3],2)]
 assert all(not x for x in linear)
 q=avg(dot(ax,ay));assert q==(F(12 if name=='plus' else -12),F(0))
 rows.append({'mode':name,'L_zero':True,'unnormalized_mean_Q12':str(q[0])})
b=avg(scale(add(dot(dx(v),dy(w)),dot(dx(w),dy(v))),F(1,2)))
assert b==(0,0)
rows.append({'mixed_mean':str(b[0]),'normalized_quadratic_values':[1,-1]})
for k in range(10,101):
 exps=[F(13*k+8,5),F(3*k-18,5),F(18*k+8,5),F(38*k+28,5),F(13*k+8,5),F(33*k+28,5)]
 assert min(exps)>F(1,5)
 assert 4*(F(k)+F(6,5)*(1-k//2)-1)>3
# General k>=10 inequalities are proved symbolically in the author text; finite sampling is auxiliary only.
print(json.dumps({'exact_Fourier_results':rows,'scale_samples':'k=10..100; auxiliary only'},indent=2))
