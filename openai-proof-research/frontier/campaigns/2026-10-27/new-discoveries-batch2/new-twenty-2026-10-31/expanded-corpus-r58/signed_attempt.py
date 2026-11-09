from pathlib import Path
import sys,random,collections,itertools,json
O=Path(__file__).resolve().parent;sys.path.insert(0,str(O/'deps'));import networkx as nx
rng=random.Random(58);n=9;M=1<<n;seen={};collisions=0

def graph(mask):
 g=nx.Graph();g.add_nodes_from(range(n));g.add_edges_from(e for i,e in enumerate(itertools.combinations(range(n),2)) if mask>>i&1);return g

def signature(adj):
 typ=[-1]*M;dp=[{} for _ in range(M)];dp[0]={(0,0):1}
 for m in range(1,M):
  v=(m&-m).bit_length()-1;B=adj[v]&m;A=m^B
  if all(adj[i]&m==(B if A>>i&1 else A) for i in range(n) if m>>i&1):typ[m]=int(bool(B))
  r=m^(1<<v);t=r;d=collections.Counter()
  while True:
   b=t|(1<<v);z=typ[b]
   if z>=0:
    for (a,c),k in dp[m^b].items():d[a+z,c+1-z]+=k
   if not t:break
   t=(t-1)&r
  dp[m]=d
 odd=collections.Counter()
 for v in range(n):odd.update(dp[(M-1)^(1<<v)])
 return (tuple(sorted(dp[-1].items())),tuple(sorted(odd.items())))
for trial in range(800):
 adj=[0]*n;mask=0
 for i,(u,v) in enumerate(itertools.combinations(range(n),2)):
  if rng.random()<[.25,.5,.75][trial%3]:mask|=1<<i;adj[u]|=1<<v;adj[v]|=1<<u
 sig=signature(adj)
 if sig in seen and mask!=seen[sig]:
  collisions+=1;old=seen[sig];iso=nx.is_isomorphic(graph(old),graph(mask));print(json.dumps({'collision':[old,mask],'isomorphic':iso}),flush=True)
  if not iso:print('NONISOMORPHIC_CANDIDATE',flush=True);break
 else:seen[sig]=mask
 if trial%100==0:print(json.dumps({'trial':trial,'signatures':len(seen),'collisions':collisions}),flush=True)
else:print('Complete: 800 seeded n9 graphs; no nonisomorphic collision of paired and vertex-deletion partition histograms. Stronger histogram equality is sufficient, not necessary, for polynomial equality.',flush=True)
