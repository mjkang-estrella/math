from pathlib import Path
from itertools import combinations
from functools import lru_cache
import json,random
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/splitmatch-review-r1')
A=[(0,1),(2,3),(4,5),(6,7)];B=[(1,2),(0,3),(5,6),(4,7)];C=[(0,2),(1,4),(3,6),(5,7)]
H=[(u,v,c) for c,es in enumerate([A,B,C]) for u,v in es]
def spectrum(N,es):
 adj=[[] for _ in range(N)]
 for u,v,c in es:adj[u].append((v,c));adj[v].append((u,c))
 @lru_cache(None)
 def f(mask):
  if not mask:return frozenset([(0,0,0)])
  b=mask&-mask;u=b.bit_length()-1;t=mask^b
  out=set(f(t))
  for v,c in adj[u]:
   if t>>v&1:
    for x in f(t^(1<<v)):
     y=list(x);y[c]+=1;out.add(tuple(y))
  return frozenset(out)
 return f((1<<N)-1)
assert len({tuple(sorted((u,v))) for u,v,c in H})==12
for es in [A,B,C]:assert sorted(x for e in es for x in e)==list(range(8))
s=spectrum(8,H);global_s={tuple(x+y for x,y in zip(p,q)) for p in s for q in s}
assert (1,3,3) not in global_s
count=0;valid=0
G=H+[(u+8,v+8,c) for u,v,c in H]
classes=[[e for e in G if e[2]==c] for c in range(3)]
for aa in combinations(classes[0],1):
 for bb in combinations(classes[1],3):
  for cc in combinations(classes[2],3):
   count+=1;vs=[v for u,w,c in aa+bb+cc for v in (u,w)]
   valid+=len(set(vs))==14
assert count==25088 and valid==0
part={0,1,6,7}
assert all((u in part)==(v in part) for u,v in A)
assert all((u in part)!=(v in part) for u,v in B+C)
assert max(sum(x) for x in s if x[0]<=1 and x[1]<=3 and x[2]<=3)==3
assert {x for x in s if sum(x)==4 and x[0]<=1}=={(0,4,0),(0,0,4)}
# Explicit source-obstruction modification: switch two C edges of two K4s.
C0=[(0,2),(1,3),(4,6),(5,7)]
source={(min(u,v),max(u,v),c) for c,es in enumerate([A,B,C0]) for u,v in es}
new={(min(u,v),max(u,v),c) for u,v,c in H}
assert source-new=={(1,3,2),(4,6,2)} and new-source=={(1,4,2),(3,6,2)}
def pms(vs):
 if not vs:yield [];return
 u=vs[0]
 for i in range(1,len(vs)):
  v=vs[i]
  for r in pms(vs[1:i]+vs[i+1:]):yield [(u,v)]+r
def eligible(N,es):
 adj=[set() for _ in range(N)]
 for u,v,c in es:adj[u].add(v);adj[v].add(u)
 unseen=set(range(N));sizes=[]
 while unseen:
  todo=[unseen.pop()];part=set(todo)
  while todo:
   u=todo.pop()
   for v in adj[u]-part:part.add(v);unseen.discard(v);todo.append(v)
  sizes.append(len(part))
 return sizes!=[4]*(N//4)
rows=[]
for N in [4,6,8]:
 a=list(zip(range(0,N,2),range(1,N,2)));sa=set(a);ps=list(pms(list(range(N))));tested=0;bad=[]
 for b in ps:
  if sa&set(b):continue
  for c in ps:
   if (sa|set(b))&set(c):continue
   es=[(u,v,i) for i,edges in enumerate([a,b,c]) for u,v in edges]
   if not eligible(N,es):continue
   tested+=1;s0=spectrum(N,es)
   missing=[(x,y,N//2-1-x-y) for x in range(N//2) for y in range(N//2-x) if (x,y,N//2-1-x-y) not in s0]
   if missing:bad.append(missing)
 assert not bad
 rows.append(dict(vertices=N,labelled_triples_fixed_A=tested,missing=bad))
rng=random.Random(381751)
for N in [10,12,14]:
 tested=0
 while tested<30:
  parts=[];used=set()
  for j in range(3):
   vs=list(range(N));rng.shuffle(vs);m=[tuple(sorted(vs[i:i+2])) for i in range(0,N,2)]
   if used&set(m):break
   used.update(m);parts.append(m)
  if len(parts)!=3:continue
  es=[(u,v,i) for i,edges in enumerate(parts) for u,v in edges]
  if not eligible(N,es):continue
  tested+=1;s0=spectrum(N,es)
  assert all((x,y,N//2-1-x-y) in s0 for x in range(N//2) for y in range(N//2-x))
 rows.append(dict(vertices=N,random_triples=tested,missing=[]))
result=dict(local_spectrum=sorted(s),global_matching_count_vectors=len(global_s),target=[1,3,3],target_exists=False,direct_selections=count,direct_witnesses=valid,small_checks=rows,source_switch_removed=sorted(source-new),source_switch_added=sorted(new-source))
(L/'mathcheck.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
