from pathlib import Path
import random,json,time,collections,itertools
L=Path(__file__).resolve().parents[1];random.seed(207);start=time.monotonic()
def valid(n,edges):
 adj=[[] for _ in range(n)]
 for u,v in edges:
  if u==v or v in adj[u]:return False
  adj[u].append(v);adj[v].append(u)
 for s in range(n):
  dist={s:0};par={s:-1};q=[s]
  for u in q:
   for v in adj[u]:
    if v not in dist:dist[v]=dist[u]+1;par[v]=u;q.append(v)
    elif v!=par[u] and dist[v]+dist[u]+1<5:return False
  if len(dist)<n:return False
 return True
def radius(n,edges):
 adj=[[] for _ in range(n)]
 for k,(u,v) in enumerate(edges):adj[u].append((v,k));adj[v].append((u,k))
 parent=[-1]*n;parent[0]=0;paths=[0]*n;q=[0];tree=set()
 for u in q:
  for v,k in adj[u]:
   if parent[v]<0:parent[v]=u;paths[v]=paths[u]^(1<<k);tree.add(k);q.append(v)
 cycles=[paths[u]^paths[v]^(1<<k) for k,(u,v) in enumerate(edges) if k not in tree];cols=[sum(((c>>k)&1)<<j for j,c in enumerate(cycles)) for k in range(len(edges))];dist=bytearray([255])*(1<<len(cycles));dist[0]=0;q=collections.deque([0])
 while q:
  u=q.popleft()
  for c in cols:
   v=u^c
   if dist[v]==255:dist[v]=dist[u]+1;q.append(v)
 return max(dist),len(dist),dist.index(max(dist))
out=[]
for n in range(10,27,2):
 seen=set();tries=0;hist={}
 while len(seen)<100 and tries<30000 and time.monotonic()-start<105:
  tries+=1;stubs=list(range(n))*3;random.shuffle(stubs);edges=sorted(tuple(sorted(stubs[j:j+2])) for j in range(0,3*n,2));key=tuple(edges)
  if key in seen or not valid(n,edges):continue
  seen.add(key);r,syndromes,s=radius(n,edges);hist[str(r)]=hist.get(str(r),0)+1
  if 10*r>3*n:
   (L/'outputs/signed-obstruction.json').write_text(json.dumps({'n':n,'edges':edges,'radius':r,'syndrome':s},indent=2));print('COUNTEREXAMPLE',n,r,edges,flush=True);break
 row={'n':n,'configuration_draws':tries,'connected_simple_girth5_labeled_samples':len(seen),'all_signature_classes_per_graph':2**(n//2+1),'radius_histogram':hist};out.append(row);print(json.dumps(row),flush=True)
 if time.monotonic()-start>=105:break
(L/'outputs/signed.json').write_text(json.dumps(out,indent=2))
