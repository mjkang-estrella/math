"""New finite instances only. No files, network, subprocess or inherited execution."""
from fractions import Fraction as F
from itertools import product,permutations
from math import comb,factorial,ceil
import random

def rank(a,p):
 a=[row[:] for row in a];i=0
 for j in range(len(a[0])):
  q=next((q for q in range(i,len(a)) if a[q][j]%p),None)
  if q is None:continue
  a[i],a[q]=a[q],a[i];v=pow(a[i][j]%p,-1,p);a[i]=[(x*v)%p for x in a[i]]
  for q in range(i+1,len(a)):
   v=a[q][j]%p
   if v:a[q]=[(x-v*y)%p for x,y in zip(a[q],a[i])]
  i+=1
  if i==len(a):break
 return i

def alphas(n,m):return [a for a in product(range(m+1),repeat=n) if sum(a)<=m]
def coefficient(u,alpha):
 v=1
 for x,a in zip(u,alpha):v*=comb(x,a) if x>=a else 0
 return v

def mixed(n):
 p=1009;perms=list(permutations(range(n)));blocks=[];cols=[]
 for outer in range(2):
  for j,perm in enumerate(perms):
   base=[0]*n;gam=[0]*n
   for i,d in enumerate(perm):base[d]=4*(n-i);gam[d]=n-1-2*i
   base[0]+=40*outer;m=j%3
   support=[tuple(x+y for x,y in zip(base,aa)) for aa in alphas(n,m)]
   blocks.append((outer,tuple(gam),m,support));cols+=support
 rows=[(o,g,aa) for o,g,m,s in blocks for aa in alphas(n,m)]
 # Local chamber exponents and local full minors, including integer translations.
 for o,g,m,supp in blocks:
  for u in supp:
   y=list(u);y[0]-=40*o
   phi=sum(abs(y[i]-y[j]) for i in range(n) for j in range(i+1,n))
   assert phi==sum(x*y0 for x,y0 in zip(g,y))
   assert all(phi>sum(gg[i]*y[i] for i in range(n)) for oo,gg,mm,ss in blocks if oo==o and gg!=g)
  assert rank([[coefficient(u,aa)%p for u in supp] for aa in alphas(n,m)],p)==len(supp)
 # Two nested levels: local permutation chambers, then coordinate cut u_1=20.
 # Search finite nonzero parameters; determinant-limit proof is in report, not this search.
 for zin in range(2,18):
  for zout in range(2,18):
   pts=[]
   for o,g,aa in rows:
    q=[pow(zin,-gg,p) for gg in g];q[0]=q[0]*pow(zout,1 if o==0 else -1,p)%p;pts.append(q)
   mat=[]
   for (_,_,aa),pt in zip(rows,pts):
    row=[]
    for u in cols:
     val=coefficient(u,aa)%p
     for d in range(n):val=val*pow(pt[d],u[d],p)%p
     row.append(val)
    mat.append(row)
   rr=rank(mat,p)
   if rr==len(rows):return dict(n=n,blocks=len(blocks),rows=len(rows),rank=rr,inner=zin,outer=zout,modulus=p)
 raise AssertionError('finite nested minor search failed')

def allocate(n,K,seed):
 rng=random.Random(seed);eps=F(1,4);M=F(1,10000);bins={};h={};groups={};requests=[];A=F(0)
 # Deliberately many levels; K=2,4 stress combinatorics only, not the local entrance theorem.
 for l in range(18):
  u=M/(1+eps)**l;hh=K*M
  while hh/2>=K*u:hh/=2
  h[l]=hh
  ws=[u*F(rng.randrange(81,101),100) for _ in range(rng.randrange(1,3*K**n+1))]
  bins[l]=ws;acc=F(0);gg=[]
  for w in ws:
   if acc+u**(n-1)*w>hh**n:gg.append(acc);acc=F(0)
   acc+=u**(n-1)*w
  if acc:gg.append(acc)
  assert all(x<=hh**n for x in gg)
  assert all(x>hh**n-u**n for x in gg[:-1])
  cost=u**(n-1)*sum(ws);assert len(gg)<=cost/(hh**n-u**n)+1
  nc=ceil(F(len(gg),factorial(n)));requests += [hh]*nc;groups[l]=gg;A+=cost
  assert factorial(n)*nc*hh**n<=cost/(1-F(1,K**n))+factorial(n)*hh**n
 Q=sum(w**n for ws in bins.values() for w in ws);C=factorial(n)*sum(x**n for x in requests)
 bound=(1+eps)**(n-1)*Q/(1-F(1,K**n))+factorial(n)*(2*K*M)**n/(1-(1+eps)**(-n))
 assert C<=bound
 # Actual placements in H-cubes using dyadic addresses; exact occupied volume check.
 H=K*M;roots=ceil(sum(x**n for x in requests)/H**n);free=[(j,(),H) for j in range(roots)];placed=[]
 for hh in sorted(requests,reverse=True):
  idx=next(i for i,x in enumerate(free) if x[2]>=hh);root,addr,side=free.pop(idx)
  while side>hh:
   side/=2
   free.extend((root,addr+(j,),side) for j in range(1,2**n));addr+=(0,)
  assert side==hh;placed.append((root,addr,hh))
 for i,(r,a,s) in enumerate(placed):
  for rr,b,ss in placed[i+1:]:assert r!=rr or not(a==b[:len(a)] or b==a[:len(b)])
 assert sum(x[2]**n for x in placed)+sum(x[2]**n for x in free)==roots*H**n
 return dict(n=n,K=K,levels=len(bins),points=sum(map(len,bins.values())),groups=sum(map(len,groups.values())),cubes=len(requests),top_cubes=roots,exact_budget=True)

def run():
 alloc=[allocate(n,K,17+n+K) for n in [2,3,4] for K in [2,4]]
 minors=[mixed(n) for n in [2,3]]
 # Continuous fractions at different roots, and repeated terminal pair in finite refinements.
 cases=0
 for R in [3,5,9]:
  for q in [3,7]:
   leaves=[]
   for s in range(R):
    t=F(1,4)+F(s+1,2*(R+1));leaves += [t/(R*q)]*q+[(1-t)/(R*q)]*q
   assert sum(leaves)==1
   for j in range(25):
    x=leaves.pop(j%len(leaves));t=F(2,5);leaves += [x*t/3]*3+[x*(1-t)/4]*4
    assert sum(leaves)==1 and len(set(leaves))<len(leaves);cases+=1
 profiles=[]
 for r in [3,11,101,1001]:
  ps=[F(2*i,r*(r+1)) for i in range(1,r+1)];assert sum(ps)==1 and len(set(ps))==r
  profiles.append(dict(r=r,max_normalized_volume=str(max(ps))))
 # Quantified convex support gap for n=3 using a rational boundary vector.
 # (3,4,5) normalized; a distinct permutation has strictly smaller support.
 a=[3,4,5];den=sum(x**3 for x in a)
 assert sum(x*x*y for x,y in zip(a,reversed(a)))<den
 return dict(status='PASS',adaptive_allocations=alloc,nested_mixed_minors=minors,continuous_finite_refinements=cases,distinct_profiles=profiles,scope='Finite instances only; no universal mathematics, contribution, priority, human or formal certification')
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
