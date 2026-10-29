from fractions import Fraction as F
import json,pathlib
P=pathlib.Path(__file__).resolve().parent
N=16;checks=0
orders=[F(-4,5),F(-3,5),F(-1,2),F(-1,5),F(0),F(1,5),F(1,2),F(4,5),F(3,2)]
def seq(v,a):
 c=[F(1)]
 for k in range(N):c.append(c[-1]*a*a/(4*(k+1)*(k+v+1)))
 return c
for v in orders:
 for u in orders:
  if u<v:continue
  for a,b in [(F(1),F(1)),(F(1),F(2)),(F(1,3),F(3,2))]:
   c,d=seq(u,a),seq(v,b); A=u*u-v*v;B=b*b-a*a;s=u+v
   h=[sum(c[k]*d[n-k] for k in range(n+1)) for n in range(N+1)]
   w=[sum(c[k]*d[n-k]*(u-v+4*k-2*n) for k in range(n+1)) for n in range(N+1)]
   for n in range(N+1):
    assert (s+2*n)*w[n]==A*h[n]-(B*h[n-1] if n else 0);checks+=1
   if u==v:
    assert w[0]==0 and w[1]==(a*a-b*b)/(2*(v+1))
# Exact rational full-series enclosure for the already PUBLIC refutation.
def S(w):
 t=F(1);L=F(0)
 for k in range(60):L+=t;t*=w/((k+1)*(F(11,10)+k))
 rho=w/(61*F(611,10));assert rho<1
 return L,L+t/(1-rho)
a,b,c,d,e,f=[S(x) for x in [F(9,16),F(225,16),F(81,4),F(81,16),F(9,4),F(225,4)]]
lo=a[0]*b[0]*c[0]**2;hi=d[1]**2*e[1]*f[1];assert lo>hi
# No numeric universal conclusions. Ivory coefficients are positive squares.
binomial=F(1)
for k in range(1,25):
 binomial*= (F(1,2)-k+1)/k
 assert binomial**2>0
r={'exact_wronskian_coefficients':checks,'orders_include_negative_sum_and_zero_sum':True,'public_midpoint_refutation_reproduced':True,'midpoint_product_ratio_lower_bound_gt_1_02':lo>F(102,100)*hi,'ivory_positive_coefficients':24,'universal_proof_by_finite_checks':False}
(P/'checks.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
