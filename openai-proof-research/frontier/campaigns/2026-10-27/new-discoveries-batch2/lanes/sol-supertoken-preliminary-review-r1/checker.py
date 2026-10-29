"""Independent exact BFS from the one-token-move definition; stdlib only."""
from itertools import combinations_with_replacement,combinations
from collections import deque
import json,datetime,pathlib
def vertices(n):
 out=[]
 for i,j in combinations_with_replacement(range(n),2):
  x=[0]*n;x[i]+=1;x[j]+=1;out.append(tuple(x))
 return out
def check(n,edges):
 V=vertices(n); idx={x:i for i,x in enumerate(V)};adj=[set() for x in V]
 for a,x in enumerate(V):
  for i in range(n):
   if x[i]:
    for j in range(n):
     if i!=j:
      y=list(x);y[i]-=1;y[j]+=1;adj[a].add(idx[tuple(y)])
 D=[]
 for a in range(len(V)):
  d={a:0};q=deque([a])
  while q:
   u=q.popleft()
   for v in adj[u]:
    if v not in d:d[v]=d[u]+1;q.append(v)
  assert len(d)==len(V)
  for b,y in enumerate(V):assert d[b]==2-sum(min(t,s) for t,s in zip(V[a],y))
  D.append(d)
 landmarks=[]
 for i,j in edges:
  x=[0]*n;x[i]+=1;x[j]+=1;landmarks.append(idx[tuple(x)])
 codes=[tuple(D[a][r] for r in landmarks) for a in range(len(V))]
 return {'n':n,'vertices':len(V),'ordered_distances_checked':len(V)**2,'landmarks':len(edges),'distinct_codes':len(set(codes))}
if __name__=='__main__':
 result=check(10,[(i,i+1) for i in [0,1,2,3,5,6,7,8]])
 assert result['distinct_codes']==55
 # P3 failure and all P5 supports, including empty.
 def code(T,m):return tuple(int(i in T)+int(i+1 in T) for i in range(m-1))
 assert code({1},3)==code({0,2},3)
 supports=[set()]+[{i} for i in range(5)]+[set(t) for t in combinations(range(5),2)]
 assert len({code(s,5) for s in supports})==16
 result.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),P5_support_codes=16,P3_singleton_pair_collision=True)
 p=pathlib.Path(__file__).with_name('checker-receipt.json');p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
