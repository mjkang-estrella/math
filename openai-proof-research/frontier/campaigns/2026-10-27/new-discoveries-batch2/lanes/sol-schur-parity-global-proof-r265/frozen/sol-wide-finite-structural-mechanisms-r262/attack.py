from explore import *
import numpy as np,random,math
random.seed(262);rng=np.random.default_rng(262)
def triples(n):return [(x-1,y-1,x+y//2-1) for x in range(1,n+1) for y in range(1,n+1) if x+y//2<=n]
def count(c,ts):return sum(c[x]==c[y]==c[z] for x,y,z in ts)
def matrix(n,ts):
 w=np.zeros((n,n),dtype=np.int64)
 for t in ts:
  for i,j in [(t[0],t[1]),(t[0],t[2]),(t[1],t[2])]:
   if i!=j:w[i,j]+=1;w[j,i]+=1
 return w
out=[]
for n in [12,13,17,23,31,47,64,96,128,192]:
 ts=triples(n);w=matrix(n,ts);s=(n+3)//6;t=(n+1)//2;u=(5*n+3)//6
 source=np.array([1 if i<s or t<=i<u else -1 for i in range(n)],dtype=np.int64)
 predicted=(n*n+5)//6;assert count(source,ts)==predicted
 best=predicted;bestc=source.copy()
 for restart in range(5):
  c=source.copy() if restart==0 else rng.choice([-1,1],size=n);field=w@c
  for step in range(12000):
   i=random.randrange(n);delta=-int(c[i]*field[i]);temp=max(.12,6*(1-step/12000))
   if delta<0 or random.random()<math.exp(-delta/temp):
    old=c[i];c[i]=-old;field-=2*old*w[:,i]
  val=count(c,ts)
  if val<best:best=val;bestc=c.copy()
 # Standard diagonal spectral majorant for the exact max-cut reformulation.
 q=w-np.diag(source*(w@source))
 lam=float(np.linalg.eigvalsh(q)[0])
 # Exact polynomial identity validation on random sign assignments, including repeats.
 for j in range(25):
  c=rng.choice([-1,1],size=n);cut=sum(int(w[i,j]) for i in range(n) for j in range(i+1,n) if c[i]!=c[j]);assert 2*count(c,ts)==2*len(ts)-cut
 rec=dict(n=n,triples=len(ts),predicted=predicted,best=best,coloring=''.join('R' if c==1 else 'B' for c in bestc),spectral_certificate_min_eigenvalue=lam,restarts=5,flips_per_restart=12000,identity_checks=25)
 out.append(rec);print(rec,flush=True)
 (L/'schur-checks.json').write_text(json.dumps(out,indent=2))
