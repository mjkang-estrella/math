import json,itertools
x=json.load(open('outputs/split.json'))[-1]['counterexample_candidate'];n,d,E,b,_=x
nei=sorted(v if u==0 else u for u,v in E if u==0 or v==0)
H=sorted((n if u==0 and (b>>nei.index(v)&1) else u,n if v==0 and (b>>nei.index(u)&1) else v) for u,v in E)+[(0,n)]
def solve(F):
 # independent static edge order, color symmetry first edge fixed 0
 colors=[];used=[set() for _ in range(n+1)];nodes=0
 def go(k):
  nonlocal nodes
  nodes+=1
  if k==len(F):return colors.copy()
  u,v=F[k]
  for c in range(d if k else 1):
   if c not in used[u] and c not in used[v]:
    colors.append(c);used[u].add(c);used[v].add(c);r=go(k+1)
    if r is not None:return r
    colors.pop();used[u].remove(c);used[v].remove(c)
  return None
 r=go(0);return r,nodes
out={'original':E,'split':H,'original_3coloring':solve(E),'deletions':[]}
for k,e in enumerate(H):
 F=H[:k]+H[k+1:];c,nodes=solve(F);odd=[]
 for S in range(1,1<<(n+1)):
  size=S.bit_count()
  if size%2 and sum((S>>u&1) and (S>>v&1) for u,v in F)>d*(size//2):odd.append(S)
 out['deletions'].append({'edge':e,'coloring':c,'backtrack_nodes':nodes,'overfull_subsets':odd})
open('outputs/split-validated.json','w').write(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
