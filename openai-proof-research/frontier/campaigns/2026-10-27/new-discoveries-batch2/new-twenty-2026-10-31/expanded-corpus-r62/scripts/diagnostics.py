import json,random,time,math,itertools
from pathlib import Path
D=Path(__file__).resolve().parents[1]; rng=random.Random(367491)
def sumsets():
 import numpy as np
 from scipy.optimize import milp,Bounds,LinearConstraint
 t=time.monotonic(); out=[]
 for z in range(240):
  n=rng.randrange(5,17); m=rng.randrange(3,n+1); delta=rng.randrange(1,min(5,m))
  if z%3==0:
   A=sorted(set(range(n//2))|set(range(n+2,n+2+n-n//2))); B=sorted(set(range(m//2))|set(range(n+2,n+2+m-m//2)))
  elif z%3==1:A=sorted(rng.sample(range(2*n),n)); B=sorted(rng.sample(range(2*n),m))
  else:A=list(range(n)); B=sorted(rng.sample(range(2*n),m))
  S=sorted({a+b for a in A for b in B}); idx={s:i for i,s in enumerate(S)}; M=np.zeros((len(B),len(S)))
  for i,b in enumerate(B):
   for a in A:M[i,idx[a+b]]=1
  r=milp(-np.ones(len(S)),integrality=np.ones(len(S)),bounds=Bounds(0,1),constraints=LinearConstraint(M,0,delta),options={'time_limit':.15,'node_limit':300})
  if r.x is None:continue
  T=[s for s,v in zip(S,r.x) if v>.5]; assert all(sum(a+b in T for a in A)<=delta for b in B)
  q=len(S)-len(T); bound=len(A)+len(B)-1-5*delta//2
  out.append(dict(A=A,B=B,delta=delta,removed=T,actual=q,conjectured_lower=bound,status=int(r.status),gap=q-bound))
  if q<bound:break
 (D/'outputs/sumset-diagnostics.json').write_text(json.dumps({'seed':367491,'cases':out,'wall':time.monotonic()-t},indent=2));print('sumsets',len(out),'min gap',min(a['gap'] for a in out),flush=True)
def cycle():
 def cc(p,j):
  n=len(p); seen=0;c=0
  for i in range(n):
   if seen>>i&1:continue
   c+=1;k=i
   while not seen>>k&1:seen|=1<<k;k=(p[k]+j)%n
  return c
 def score(p):return sum(max(0,cc(p,j)-2) for j in range(len(p)))
 out=[];t=time.monotonic()
 for n in [9,15,21,25]:
  best=999;bp=None;steps=0
  for restart in range(6):
   p=list(range(n));rng.shuffle(p);s=score(p)
   for z in range(5000):
    a,b=rng.sample(range(n),2);p[a],p[b]=p[b],p[a];v=score(p);temp=.15+.9*(1-z/5000)
    if v<=s or rng.random()<math.exp((s-v)/temp):s=v
    else:p[a],p[b]=p[b],p[a]
    steps+=1
    if s<best:best=s;bp=p[:]
    if best==0:break
   if best==0:break
  out.append(dict(n=n,best_defect=best,permutation=bp,cycle_counts=[cc(bp,j) for j in range(n)],steps=steps));print('cycle',n,best,flush=True)
 (D/'outputs/cycle-diagnostics.json').write_text(json.dumps({'seed':367491,'cases':out,'wall':time.monotonic()-t},indent=2))
def shuffle():
 from functools import lru_cache
 @lru_cache(maxsize=20000)
 def sq(w):
  states={''}
  for ch in w:
   nxt=set()
   for q in states:
    nxt.add(q+ch)
    if q and q[0]==ch:nxt.add(q[1:])
   states=nxt
   if len(states)>100000:raise RuntimeError('state cap')
  return '' in states
 def cuts(w):
  if sq(w):return 0
  n=len(w)
  if any(sq(w[i:]+w[:i]) for i in range(1,n)):return 1
  for i in range(1,n):
   for j in range(i+1,n):
    blocks=(w[:i],w[i:j],w[j:])
    for p in itertools.permutations(blocks):
     if sq(''.join(p)):return 2
  return 3
 out=[];t=time.monotonic()
 for n in range(2,15,2):
  counts=[0]*4
  for w in itertools.product('01',repeat=n):
   if w.count('1')%2:continue
   w=''.join(w); counts[cuts(w)]+=1
  out.append(dict(length=n,counts=counts));print('shuffle',n,counts,flush=True)
 # Source witness must require two cuts: tests DP and permutation semantics.
 witness='111110110000111100010000';a=cuts(witness);assert a==2
 (D/'outputs/shuffle-diagnostics.json').write_text(json.dumps({'exhaustive':out,'source_witness':witness,'source_witness_cuts':a,'wall':time.monotonic()-t},indent=2))
if __name__=='__main__':
 import sys
 {'sumsets':sumsets,'cycle':cycle,'shuffle':shuffle}[sys.argv[1]]()
