"""Bounded exact finite tests, not a universal proof or a solver-certified lower bound."""
from pathlib import Path
from itertools import combinations
import random,json,time
P=Path(__file__).parent

def connected(n,es):
 seen={0}
 while True:
  old=len(seen)
  for u,v in es:
   if u in seen or v in seen:seen.update((u,v))
  if old==len(seen):return len(seen)==n

def trees(n,es):
 out=[]
 for cs in combinations(range(len(es)),n-1):
  pa=list(range(n))
  def root(v):
   while pa[v]!=v:v=pa[v]
   return v
  for i in cs:
   u,v=es[i];u,v=root(u),root(v)
   if u==v:break
   pa[u]=v
  else:out.append(sum(1<<i for i in cs))
 return out

def test(n,es):
 m=len(es);k=min(sum(((s>>u)^(s>>v))&1 for u,v in es) for s in range(1,1<<(n-1)))
 if k<3:return None
 ts=trees(n,es);fs=[sum(1<<i for i in c) for c in combinations(range(m),k-1)]
 covers=[sum(1<<i for i,f in enumerate(fs) if f&t==0) for t in ts]
 left=(1<<len(fs))-1;chosen=[]
 while left:
  j=max(range(len(ts)),key=lambda j:(covers[j]&left).bit_count())
  gain=(covers[j]&left).bit_count()
  if not gain:raise RuntimeError('enumerator failed completeness or graph connectivity')
  chosen.append(ts[j]);left&=~covers[j]
 # Exact verification independently from stored incidence table.
 assert all(any(t&f==0 for t in chosen) for f in fs)
 assert all(t.bit_count()==n-1 and connected(n,[e for i,e in enumerate(es) if t>>i&1]) for t in chosen)
 return {'n':n,'edges':es,'lambda':k,'spanning_trees':len(ts),'failure_sets':len(fs),'family_masks':chosen,'family_size':len(chosen),'bound':m,'exact_verified':True,'obstruction':len(chosen)>m,'note':'greedy excess is not a lower bound'}
if __name__=='__main__':
 rng=random.Random(320847);out=[];attempts=0;start=time.time()
 while len(out)<45 and attempts<500:
  attempts+=1;n=rng.choice([6,7,8]);es=[e for e in combinations(range(n),2) if rng.random()<.65]
  if len(es)>18 or not connected(n,es):continue
  r=test(n,es)
  if r:out.append(r)
 (P/'ubb-runs.json').write_text(json.dumps({'attempts':attempts,'elapsed':time.time()-start,'graphs':out},indent=2))
 print({'graphs':len(out),'attempts':attempts,'max_ratio':max(r['family_size']/r['bound'] for r in out),'greedy_excesses':sum(r['obstruction'] for r in out),'elapsed':time.time()-start})
