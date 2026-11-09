from functools import lru_cache
from pathlib import Path
import json,resource
resource.setrlimit(resource.RLIMIT_AS,(600*1024**2,600*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(50,50))
def parts(n,lo=1,hi=100):
 if n==0:yield ()
 for x in range(lo,min(n,hi)+1):
  for t in parts(n-x,x,hi):yield (x,)+t
@lru_cache(maxsize=100000)
def embed(forest,caps,prev=-1,left=0):
 if sum(caps)<sum(forest)+left:return False
 if left==0:
  if not forest:return True
  return embed(forest[1:],caps,-1,forest[0])
 for i,c in enumerate(caps):
  if i==prev or c==0:continue
  if i>0 and caps[i-1]==c and i-1!=prev:continue
  cs=list(caps);cs[i]-=1
  if embed(forest,tuple(cs),i,left-1):return True
 return False
rows=[];bad=[]
for n in range(2,9):
 count=0
 for m in range(n+1,2*n):
  for fs in parts(m):
   if max(fs)<2:continue
   o=sum(x%2 for x in fs);r=max(2*n-1,(3*m+1)//2-1,m+n-o-2)
   for cs in parts(r,hi=n-1):
    # A hub in a clique cannot have a forest neighbour in that clique.
    count+=1;ok=False
    for j in set(cs):
     caps=list(cs);caps.remove(j)
     if embed(tuple(sorted(fs,reverse=True)),tuple(caps)):ok=True;break
    if not ok:bad.append({'n':n,'m':m,'forest':fs,'cliques':cs,'R_conjectured':r})
 rows.append({'n':n,'cluster_graph_forest_pairs':count});print(n,count,len(bad),flush=True)
Path(__file__).with_name('cluster-diagnostic.json').write_text(json.dumps({'scope':'all disjoint unions of cliques of size < n on conjectured R vertices, all nonempty path-component forests; Python exact search, not Lean','rows':rows,'counterexamples':bad},indent=2))
