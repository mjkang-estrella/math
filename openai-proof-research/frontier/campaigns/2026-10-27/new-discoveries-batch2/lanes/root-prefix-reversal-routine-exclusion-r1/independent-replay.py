import json,math,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
results=[]
count=boundary=trees=0
for n in range(4,91):
 for k in range(2,n-1):
  for m in range(k+1,n):
   par=list(range(n));edges=[]
   def root(x):
    while par[x]!=x:par[x]=par[par[x]];x=par[x]
    return x
   for q in (n,m,k):
    for x in range(q//2):
     y=q-1-x;par[root(x)]=root(y);edges.append((x,y,q))
   connected=len({root(x) for x in range(n)})==1
   a=n-m
   if n>2*k+2 and a<=k+1 and math.gcd(a,n-k)==1:
    assert connected;count+=1;boundary+=a==k+1
   if n%2==0 and m+k<n and connected:
    assert len(edges)==n-1
    adj=[[] for _ in range(n)]
    for x,y,q in edges:adj[x].append((y,q==n));adj[y].append((x,q==n))
    color={0:0};todo=[0]
    while todo:
     x=todo.pop()
     for y,b in adj[x]:
      if y not in color:color[y]=color[x]^b;todo.append(y)
    assert sum(color.values())==n//2
    for q in (n,m,k):
     assert all(color[x]^color[q-1-x if x<q else x]==(q==n) for x in range(n))
    trees+=1
data=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),replays=results,independent_orbits=count,boundary_a_kplus1=boundary,tree_block_controls=trees,scope='n<=90; finite controls only')
(L/'independent-checks.json').write_text(json.dumps(data,indent=2));print(json.dumps(data))
