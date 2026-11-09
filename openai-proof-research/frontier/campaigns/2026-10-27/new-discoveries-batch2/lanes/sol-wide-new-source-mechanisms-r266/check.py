from pathlib import Path
from itertools import combinations
import json,time
L=Path(__file__).resolve().parent
out=[]
for n in range(3,7):
 pairs=list(combinations(range(n),2));counts=dict(n=n,graphs=0,connected_alpha3_KE=0,maximal_hypothesis=0,failures=[])
 for bits in range(1<<len(pairs)):
  counts['graphs']+=1;adj=[0]*n;deg=[0]*n;m=bits.bit_count()
  for k,(i,j) in enumerate(pairs):
   if bits>>k&1:adj[i]|=1<<j;adj[j]|=1<<i;deg[i]+=1;deg[j]+=1
  seen=1
  for _ in range(n):
   for i in range(n):
    if seen>>i&1:seen|=adj[i]
  if seen!=(1<<n)-1:continue
  inds=[s for s in range(1<<n) if all(not(adj[i]&s) for i in range(n) if s>>i&1)]
  if max(s.bit_count() for s in inds)!=3:continue
  def match(s):
   if not s:return 0
   i=(s&-s).bit_length()-1;t=s^(1<<i)
   return max([match(t)]+[1+match(t^(1<<j)) for j in range(n) if t>>j&1 and adj[i]>>j&1])
  if match((1<<n)-1)!=n-3:continue
  counts['connected_alpha3_KE']+=1;maxs=[s for s in inds if s.bit_count()==3]
  if not all(all(sum(deg[i] for i in range(n) if s>>i&1)+deg[j]>m for j in range(n) if not s>>j&1) for s in maxs):continue
  counts['maximal_hypothesis']+=1;ds=sorted(deg);h=max(k for k in range(n+1) if sum(ds[:k])<=m)
  if h!=3:counts['failures'].append(dict(edges=[e for k,e in enumerate(pairs) if bits>>k&1],h=h,degree=deg))
 out.append(counts)
(L/'exact-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
