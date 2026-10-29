import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(10,10));signal.alarm(15)
from pathlib import Path
import json
from math import isqrt
# Sparse exact Z[p,a,r]; denominator-cleared identity, no candidate code.
def add(*xs):
 z={}
 for x in xs:
  for k,v in x.items():z[k]=z.get(k,0)+v
 return {k:v for k,v in z.items() if v}
def scale(x,n):return {k:v*n for k,v in x.items() if v*n}
def mul(x,y):
 z={}
 for i,a in x.items():
  for j,b in y.items():
   k=tuple(s+t for s,t in zip(i,j));z[k]=z.get(k,0)+a*b
 return {k:v for k,v in z.items() if v}
p={(1,0,0):1};a={(0,1,0):1};r={(0,0,1):1}
pa=add(p,scale(a,-1));ar=add(a,scale(r,-1))
left=add(mul(scale(a,2),mul(p,add(p,scale(r,-1)))),scale(mul(ar,add(scale(mul(p,p),3),scale(mul(a,r),-2))),-1))
right=add(mul(add(scale(r,3),scale(a,-1)),mul(pa,pa)),mul(scale(a,2),mul(add(scale(r,2),scale(a,-1)),pa)),mul(a,mul(ar,add(scale(r,2),scale(a,-1)))))
assert left==right
prime=lambda n:n>=2 and all(n%d for d in range(2,isqrt(n)+1))
small=[]
for pp in [2,3,5,7]:
 for rr in range(1,pp):
  aa=next(n for n in range(rr+1,2*rr+1) if prime(n))
  if pp*pp>=11*aa:continue
  qq=next(n for n in range(pp*pp//aa+1,100) if prime(n))
  assert aa*qq>pp*pp and 0<(aa-rr)*(qq-rr)<=pp*(pp-rr)
  small.append([rr,pp,aa,qq,aa*qq,(aa-rr)*(qq-rr),pp*(pp-rr)])
assert len(small)==10
out={'status':'PASS','integer_polynomial_identity':True,'small_exception_rows':sorted(small),'scope':'Only identity and complete p<11 exception arithmetic; all-order prime-gap input external, no source/full-formal PASS'}
(Path(__file__).parent/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
