import math,random,json,time
from pathlib import Path
from functools import lru_cache
import sympy as S
P=Path(__file__).resolve().parent;x=S.Symbol('x');rng=random.Random(60)
def size(t):return t[0]+sum(map(size,t[1]))
def conv(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,u in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=u*v
 return c
@lru_cache(maxsize=4096)
def heights(t,m):
 r,ch=t;n=size(t);w=[1]
 for c in ch:w=conv(w,heights(c,m))
 return tuple(sum(w[j-l]*math.comb(r+l-1,l) for l in range(max(0,j-len(w)+1),j+1)) for j in range(m*n+1))
def ehr(t):
 n=size(t);vs=[sum(heights(t,m)) for m in range(n+1)];a=vs[:];f=S.Poly(0,x,domain=S.QQ);b=S.Poly(1,x,domain=S.QQ)
 for k in range(n+1):
  f+=b.mul_ground(a[0]);a=[a[i+1]-a[i] for i in range(len(a)-1)];b=b*S.Poly(x-k,x,domain=S.QQ).mul_ground(S.Rational(1,k+1))
 assert f.degree()==n and f.eval(n+1)==sum(heights(t,n+1))
 return f

def randtree(n):
 if n==1:return (1,())
 r=rng.randint(1,min(4,n));left=n-r;ch=[]
 while left:
  z=rng.randint(1,left);ch.append(randtree(z));left-=z
 return (r,tuple(ch))
records=[];start=time.monotonic()
# All two-block compositions through dimension 14, plus genuinely branching arbors.
cases=[(r,((n-r,()),)) for n in range(2,15) for r in range(1,n)]
cases += [randtree(n) for n in range(13,25) for _ in range(3)]
for i,t in enumerate(cases):
 f=ehr(t);sq=f.sqf_list()[1];real=sum(g.count_roots(-1,0)*e for g,e in sq);row=dict(tree=t,dimension=size(t),coeffs=list(map(str,f.all_coeffs())),roots_in_interval=int(real),pass_interval=(real==f.degree()));records.append(row)
 print(i,len(cases),size(t),real,flush=True)
 (P/'checks.json').write_text(json.dumps(dict(cases=records,elapsed=time.monotonic()-start),indent=2))
 if real!=f.degree():print('COUNTEREXAMPLE',row,flush=True);break
print('DONE',len(records),flush=True)
