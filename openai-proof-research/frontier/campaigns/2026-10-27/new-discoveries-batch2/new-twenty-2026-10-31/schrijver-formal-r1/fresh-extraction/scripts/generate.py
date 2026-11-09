"""Own compressed-coordinate generator and literal edge/BFS checker. No imports of input code."""
from pathlib import Path
from itertools import combinations
from collections import deque
import json
lane=Path(__file__).resolve().parent.parent
summary=[]
for n in (27,28):
 k=12
 # Removing the mandatory gap after each selected element gives an ordinary combination.
 V=sorted(sum(1<<(x+i) for i,x in enumerate(c)) for c in combinations(range(n-k+1),k) if not(c[0]==0 and c[-1]+k-1==n-1))
 review=json.loads((lane/f'inputs/leads-review-r122/outputs/graph-{n}-{k}-certificate.json').read_text())
 assert set(V)==set(review['vertices'])
 assert len(V)==len(set(V))
 index={a:i for i,a in enumerate(V)}
 adj=[[j for j,b in enumerate(V) if a!=b and a&b==0] for a in V]
 def bfs(s):
  d=[-1]*len(V);p=[s]*len(V);d[s]=0;q=deque([s])
  while q:
   u=q.popleft()
   for v in adj[u]:
    if d[v]<0:d[v]=d[u]+1;p[v]=u;q.append(v)
  assert min(d)>=0
  assert all(d[v]<=d[u]+1 for u in range(len(V)) for v in adj[u])
  assert all(v==s or (p[v] in adj[v] and d[p[v]]+1==d[v]) for v in range(len(V)))
  return d,p
 seen=set();trees=[];D=0;pair=None;lower=None
 for s,a in enumerate(V):
  if a in seen:continue
  orbit=[index[((a<<t)|(a>>(n-t)))&((1<<n)-1)] for t in range(n)]
  seen.update(V[i] for i in orbit)
  d,p=bfs(s);trees.append(dict(source=s,labels=d,parents=p,orbit=orbit))
  if max(d)>D:
   D=max(d);pair=[s,d.index(D)];lower=d
 assert seen==set(V)
 # Cross-check every independent review representative's complete distance labelling.
 by_orbit={}
 for tree in trees:
  a=V[tree['source']]
  for t in range(n):by_orbit[((a<<t)|(a>>(n-t)))&((1<<n)-1)]=(tree,t)
 for rs,levels in review['representative_levels']:
  tree,t=by_orbit[review['vertices'][rs]]
  for j,b in enumerate(review['vertices']):
   inv=((b>>(t))|(b<<(n-t)))&((1<<n)-1)
   expected=next(i for i,l in enumerate(levels) if l>>j&1)
   assert tree['labels'][index[inv]]==expected
 data=dict(n=n,k=k,vertices=V,trees=trees,lower_labels=lower,pair=pair,diameter=D)
 (lane/f'outputs/certificate-{n}.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
 row=dict(n=n,k=k,vertices=len(V),edges=sum(map(len,adj))//2,representatives=len(trees),diameter=D,pair_masks=[V[i] for i in pair],pair_one_based=[[j+1 for j in range(n) if V[i]>>j&1] for i in pair],crosscheck='every review representative and every vertex label')
 summary.append(row);print(json.dumps(row),flush=True)
 if n==27:
  # Compact kernel-checked data sample: every mask, cardinality and cycle stability.
  text='import Checkers\nset_option maxRecDepth 10000\nset_option maxHeartbeats 5000000\nnamespace Schrijver\ndef masks27 : List Nat := ['+','.join(map(str,V))+']\n'
  text+='theorem masks27_valid : (masks27.all (validMask 27 12)) = true := by decide\n'
  text+='theorem masks27_count : masks27.length = 819 := by decide\n'
  text+=f'def witnessA : Nat := {V[pair[0]]}\ndef witnessB : Nat := {V[pair[1]]}\n'
  text+='theorem witness_valid : validMask 27 12 witnessA && validMask 27 12 witnessB = true := by decide\n'
  text+='end Schrijver\n'
  (lane/'src/Data27.lean').write_text(text)
(lane/'outputs/computation.json').write_text(json.dumps(summary,indent=2)+'\n')
