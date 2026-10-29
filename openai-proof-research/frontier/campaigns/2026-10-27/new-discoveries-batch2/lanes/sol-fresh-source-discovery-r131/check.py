import itertools,math,json,sys,random
from pathlib import Path
from functools import lru_cache
L=Path(__file__).resolve().parent
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def parts(mask):
 if not mask:yield ();return
 bit=mask&-mask;rest=mask^bit;s=rest
 while True:
  for p in parts(rest^s):yield (s|bit,)+p
  if not s:break
  s=(s-1)&rest
def polys(n,edges):
 adj=[0]*n
 for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
 @lru_cache(None)
 def connected(s):
  seen=s&-s;front=seen
  while front:
   b=front&-front;front^=b;new=adj[b.bit_length()-1]&s&~seen;seen|=new;front|=new
  return seen==s
 @lru_cache(None)
 def mu(s):
  k=s.bit_count()
  if k==1:return (1,)
  out=[0]*k
  for p in parts(s):
   if len(p)==1 or not all(connected(t) for t in p):continue
   a=[1]*len(p)
   for t in p:a=mul(a,mu(t))
   for i,v in enumerate(a):out[i]-=v
  return tuple(out)
 full=(1<<n)-1
 return tuple((-1)**(n-1)*x for x in mu(full)) if connected(full) else None
def gamma(a):
 a=list(a);d=len(a)-1;g=[]
 for i in range(d//2+1):
  v=a[i];g.append(v)
  for j in range(d-2*i+1):a[i+j]-=v*math.comb(d-2*i,j)
 assert not any(a)
 return g
def root_test(a):
 # exact Sturm count, with distinct real roots and square-free part.
 import sympy as S
 t=S.Symbol('t');p=S.Poly.from_list(list(reversed(a)),t)
 if p.is_zero:return True,None
 q=p.sqf_part();nr=q.count_roots(-S.oo,S.oo)
 return nr==q.degree(),dict(distinct_real=int(nr),squarefree_degree=q.degree(),factor=str(S.factor(p.as_expr())))
if __name__=='__main__':
 rng=random.Random(131);records=[];fail=[]
 for n in range(3,9):
  E=list(itertools.combinations(range(n),2))
  for z in range(32):
   H={(i,i+1) for i in range(n-1)}
   H|={e for e in E if rng.random()<.2}
   G=H|{e for e in E if rng.random()<.4}
   a=polys(n,G);b=polys(n,H);d=[x-y for x,y in zip(a,b)];g=gamma(d)
   ok,root=root_test(d)
   r=dict(n=n,G=sorted(G),H=sorted(H),g=a,h=b,difference=d,gamma=g,realroot=ok,root_certificate=root)
   records.append(r)
   if not ok or min(g)<0:fail.append(r);print(json.dumps(r),flush=True)
   if fail:break
  if fail:break
 out=dict(scope='Seed131, at most32 connected nested labeled pairs per n=3..8; not exhaustive',cases=len(records),failures=fail,records=records)
 (L/'check-results.json').write_text(json.dumps(out,indent=2));print('cases',len(records),'failures',len(fail))
