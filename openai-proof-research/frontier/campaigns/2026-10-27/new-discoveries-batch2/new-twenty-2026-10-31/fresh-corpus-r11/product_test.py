import math,json,time
from pathlib import Path
p=Path(__file__).parent
def divisors(n): return [i for i in range(1,n+1) if n%i==0]
def f(N,e,r): return min(d*(2*((r+d-1)//d)-1) for a in divisors(N//e) if a*e>=r for b in divisors(e) for d in [a*b])
# All abstract N,e pairs with prime support equal; only realizable elementary-divisor choices used.
groups=[]
for n in range(2,65):
 for e in divisors(n):
  if e>1 and all(e%q==0 for q in divisors(n) if q>1 and all(q%k for k in range(2,math.isqrt(q)+1))):
   groups.append((n,e,[f(n,e,r) for r in range(1,n+1)]))
t=time.time(); checked=0; bad=[]
for N1,e1,F1 in groups:
 for N2,e2,F2 in groups:
  if N1*N2>2048:continue
  N=N1*N2;e=math.lcm(e1,e2); F=[f(N,e,r) for r in range(1,N+1)]
  for r1,v1 in enumerate(F1,1):
   for r2,v2 in enumerate(F2,1):
    checked+=1
    if F[r1*r2-1]>v1*v2:bad.append([N1,e1,r1,v1,N2,e2,r2,v2,F[r1*r2-1]])
r=dict(scope='product obstruction only, factors order <=64, product order <=2048; no theorem inference from no counterexample',checks=checked,bad=bad[:30],seconds=time.time()-t)
(p/'product-diagnostics.json').write_text(json.dumps(r,indent=2));print(r)
