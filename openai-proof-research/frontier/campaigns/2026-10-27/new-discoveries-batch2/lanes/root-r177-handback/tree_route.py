import itertools,json,heapq,collections
from pathlib import Path
L=Path(__file__).resolve().parent
def tree(seq,n):
 d=[1]*n
 for u in seq:d[u]+=1
 leaves=[u for u in range(n) if d[u]==1];heapq.heapify(leaves);E=[]
 for u in seq:
  v=heapq.heappop(leaves);E.append((u,v));d[u]-=1
  if d[u]==1:heapq.heappush(leaves,u)
 E.append(tuple(leaves));return E
counts=collections.Counter();bad=[];max_twos={};example={}
for n in range(3,8):
 for seq in itertools.product(range(n),repeat=n-2):
  E=tree(seq,n);m=len(E);d=[sum(v in e for e in E) for v in range(n)];best=None
  # x_e=2+2*1_F(e), closed spanning Euler walk, cost=2m+2|F|.
  for k in range(m//2+1):
   for F in itertools.combinations(range(m),k):
    s=[3*v for v in d]
    for i in F:
     u,v=E[i];s[u]+=2;s[v]+=2
    if all(s[u]!=s[v] for u,v in E):best=k;break
   if best is not None:break
  counts[n]+=1
  if best is None:
   bad.append(dict(n=n,prufer=seq,edges=E));break
  if best>max_twos.get(n,-1):max_twos[n]=best;example[n]=dict(edges=E,F=F)
 # Stop a failed order rather than falsely claim its remaining sequences.
out=dict(scope='Restricted closed spanning walk ansatz only, not full source scope.',tested=dict(counts),failed=bad,maximum_minimum_number_of_4_edges=max_twos,extremizers=example)
(L/'tree-route.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
