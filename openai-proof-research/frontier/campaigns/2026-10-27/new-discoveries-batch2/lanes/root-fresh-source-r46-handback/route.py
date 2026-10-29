import math,json,time,pathlib
from sympy import Poly,Symbol,oo,expand
p=pathlib.Path(__file__).resolve().parent;x=Symbol('x');start=time.monotonic();out=[]
# Focused exact root-count check; no numerical root solver.
for m in [5,6]:
 a=[[1]]
 for n in range(1,61):
  row=[0]*(n+1)
  for j in range(1,min(n,m)+1):
   for k,v in enumerate(a[n-j]):row[k+1]+=math.comb(n-1,j-1)*v
  a.append(row)
  # Independently compare source's differential-delay recurrence.
  b=[0]*(n+1)
  for k,v in enumerate(a[n-1]):b[k]+=k*v;b[k+1]+=v
  if n>m:
   for k,v in enumerate(a[n-m-1]):b[k+1]-=math.comb(n-1,m)*v
  assert b==row
  if n in [40,60]:
   lo=next(k for k,v in enumerate(row) if v);f=Poly.from_list(row[lo:][::-1],x)
   nr=int(f.count_roots(-oo,oo));r={'n':n,'m':m,'deflated_degree':f.degree(),'distinct_real_roots':nr};out.append(r);print(r,flush=True)
# Uniform multiplier preserver obstruction at the first nontrivial cap 5 row.
q=Poly(expand((1+x)**6-1-6*x),x);assert q==Poly(x**6+6*x**5+15*x**4+20*x**3+15*x**2,x)
assert q.count_roots(-oo,oo)==1
# q''=30(1+x)^4, q'(0)=q(0)=0: strict convex tangent => q(x)>0 for x!=0.
assert q.diff().diff()==Poly(30*(1+x)**4,x)
f=Poly(x**4+15*x**3+65*x**2+90*x+31,x)
assert f.count_roots(-oo,oo)==4 # Actual B6,cap5/x^2, in contrast to the generic symbol.
(p/'route-checks.json').write_text(json.dumps({'roots':out,'obstruction':str(q.as_expr()),'seconds':time.monotonic()-start},indent=2))
