"""Exact finite A-type diagnostic; not a uniform-rank proof."""
import itertools,json,time
from functools import lru_cache

def edge(p):
 n=len(p); pos=[0]*n
 for i,v in enumerate(p):pos[v]=i
 pred=[0]*n
 for i in range(n):
  for j in range(i+1,n):
   if pos[i]>pos[j]:pred[j]|=1<<i
 @lru_cache(None)
 def dp(mask,last):
  if mask==(1<<n)-1:return True
  for j in range(n):
   if not (mask>>j)&1 and pred[j]&mask==pred[j] and (last==n or not ((pred[j]>>last)&1)):
    if dp(mask|1<<j,j):return True
  return False
 return dp(0,n)

def run(n):
 ps=list(itertools.permutations(range(n))); ix={p:i for i,p in enumerate(ps)}
 gens=[p for p in ps[1:] if edge(p)]
 dist={ps[0]:0};layer=[ps[0]]
 while layer:
  nxt=[]
  for p in layer:
   for g in gens:
    q=tuple(p[g[i]] for i in range(n))
    if q not in dist:dist[q]=dist[p]+1;nxt.append(q)
  layer=nxt
 return dict(type='A'+str(n-1),vertices=len(ps),generators=len(gens),diameter=max(dist.values()),histogram={str(k):sum(v==k for v in dist.values()) for k in set(dist.values())},complete=len(dist)==len(ps))
if __name__=='__main__':
 out=[run(n) for n in range(3,7)];open('weyl-diagnostic.json','w').write(json.dumps(out,indent=2));print(out)
