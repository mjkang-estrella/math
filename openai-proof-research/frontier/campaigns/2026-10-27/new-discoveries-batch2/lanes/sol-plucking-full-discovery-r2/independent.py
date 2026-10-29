import json,itertools,functools
from pathlib import Path
from structured import calc,uni

def literal(par,ds):
 children={i:[] for i in range(len(par))}
 for v,p in enumerate(par):
  if p>=0:children[p].append(v)
 @functools.lru_cache(None)
 def rec(active,delays):
  if not active:return (1,)
  aset=set(active);d=dict(delays);out=[0]
  for v in active:
   if any(c in aset for c in children[v]) or d[v]!=1:continue
   r=0;w=v
   def size(x):return 0 if x not in aset else 1+sum(size(c) for c in children[x])
   while par[w]>=0:
    sib=children[par[w]];r+=sum(size(s) for s in sib[sib.index(w)+1:]);w=par[w]
   nxt=tuple(x for x in active if x!=v);ns=set(nxt)
   nd=tuple((x,max(1,d[x]-1) if x in d else 1) for x in nxt if not any(c in ns for c in children[x]))
   q=rec(nxt,nd)
   out.extend([0]*max(0,len(q)+r-len(out)))
   for i,a in enumerate(q):out[i+r]+=a
  while len(out)>1 and not out[-1]:out.pop()
  return tuple(out)
 return rec(tuple(range(1,len(par))),tuple(sorted(ds.items())))

def direct(par,ds):
 n=len(par)-1;anc={}
 for v in range(1,n+1):
  anc[v]=set();p=par[v]
  while p>0:anc[v].add(p);p=par[p]
 pairs=[(u,v) for u in range(1,n+1) for v in range(u+1,n+1) if u not in anc[v] and v not in anc[u]] # vertices in preorder
 out=[0];legal=0
 for perm in itertools.permutations(range(1,n+1)):
  pos={v:i+1 for i,v in enumerate(perm)}
  if any(pos[v]>pos[a] for v in anc for a in anc[v]) or any(pos[v]<d for v,d in ds.items()):continue
  ex=sum(pos[u]<pos[v] for u,v in pairs)
  out.extend([0]*max(0,ex+1-len(out)));out[ex]+=1;legal+=1
 return tuple(out),legal

rows=json.loads(Path('structured-checks.json').read_text());count=0
for r in rows:
 q=literal(r['parents'],dict(zip(r['leaves'],r['delays'])));assert q==tuple(r['Q']);count+=1
cases=[([-1,0,1,1,0,4,4],{2:3,3:1,5:1,6:2}),([-1,0,1,2,2,0,5],{3:3,4:1,6:2}),([-1,0,1,1,0,4,5,5],{2:3,3:1,6:1,7:2})]
checks=[]
for p,d in cases:
 q,n=direct(p,d);assert q==literal(p,d)==calc(p,d)[0];checks.append(dict(parents=p,delays=d,Q=q,legal_orders=n,permutations_tested=__import__('math').factorial(len(p)-1)))
Path('independent-checks.json').write_text(json.dumps(dict(literal_comparisons=count,direct_enumerations=checks),indent=2));print('literal comparisons',count,'direct-order cases',len(checks),'PASS')
