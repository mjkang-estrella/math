from pathlib import Path
import itertools,collections,json
D=Path(__file__).resolve().parent
out=[]
for r in [2,3]:
 V=list(itertools.product(range(3),repeat=r))
 adj={v:[w for w in V if sum(abs(a-b) for a,b in zip(v,w))==1] for v in V}
 dist={}
 for v in V:
  ds={v:0};Q=collections.deque([v])
  while Q:
   a=Q.popleft()
   for b in adj[a]:
    if b not in ds:ds[b]=ds[a]+1;Q.append(b)
  assert len(ds)==len(V);dist[v]=ds
  assert all(ds[w]==sum(abs(a-b) for a,b in zip(v,w)) for w in V)
 degrees=set();trans=set();edges=0
 for v in V:
  k=sum(a!=1 for a in v)
  assert len(adj[v])==2*r-k
  assert sum(dist[v].values())==3**(r-1)*(2*r+k)
  degrees.add(len(adj[v]));trans.add(sum(dist[v].values()))
  for w in adj[v]:
   if v<w:
    a=sum(dist[v][z]<dist[w][z] for z in V);b=sum(dist[w][z]<dist[v][z] for z in V)
    assert sorted([a,b])==[3**(r-1),2*3**(r-1)];edges+=1
 assert len(degrees)==len(trans)==r+1
 out.append({'r':r,'vertices':len(V),'edges':edges,'degrees':sorted(degrees),'transmissions':sorted(trans),'lambda':2})
(D/'exact-check.json').write_text(json.dumps({'status':'PASS','cases':out},indent=2)+'\n');print(json.dumps(out))
