import random,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(338917)
def graph(n,steps):
 faces={tuple(sorted((0,i,2+(i-1)%(n-2)))) for i in range(2,n)}|{tuple(sorted((1,i,2+(i-1)%(n-2)))) for i in range(2,n)}
 # bipyramid over the (n-2)-cycle, vertices 0 and 1 the apices
 for _ in range(steps):
  edgefaces={}
  for f in faces:
   for i in range(3):edgefaces.setdefault(tuple(sorted((f[i],f[(i+1)%3]))),[]).append(f)
  u,v=rng.choice(list(edgefaces));fs=edgefaces[u,v]
  if len(fs)!=2:continue
  a=next(x for x in fs[0] if x not in (u,v));b=next(x for x in fs[1] if x not in (u,v))
  if tuple(sorted((a,b))) in edgefaces:continue
  deg=[0]*n
  for e in edgefaces:
   for x in e:deg[x]+=1
  if deg[u]<=3 or deg[v]<=3:continue
  faces.difference_update(fs);faces.add(tuple(sorted((a,b,u))));faces.add(tuple(sorted((a,b,v))))
 adj=[set() for _ in range(n)]
 for f in faces:
  for i in f:adj[i].update(set(f)-{i})
 assert len(faces)==2*n-4 and sum(map(len,adj))==6*n-12
 return adj,faces

def check(adj,faces):
 n=len(adj);col=[-1]*n;classes=[0]*4;out=[];overflow=False
 for c,v in enumerate(next(iter(faces))):col[v]=c;classes[c]|=1<<v
 def dfs():
  nonlocal overflow
  if overflow:return
  un=[i for i in range(n) if col[i]<0]
  if not un:
   out.append(tuple(classes))
   if len(out)>10000:overflow=True
   return
  def forbidden(i):return {col[j] for j in adj[i] if col[j]>=0}
  v=max(un,key=lambda i:(len(forbidden(i)),len(adj[i])))
  bad=forbidden(v)
  for c in range(4):
   if c in bad:continue
   col[v]=c;classes[c]|=1<<v;dfs();classes[c]^=1<<v;col[v]=-1
 dfs()
 if overflow:return {'overflow':True,'colorings_lower_bound':len(out)}
 parent=list(range(len(out)));seen={}
 def find(i):
  while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
  return i
 parity={}
 for k,cs in enumerate(out):
  for cl in cs:
   if cl in seen:parent[find(k)]=find(seen[cl])
   else:seen[cl]=k
 for k,cs in enumerate(out):
  p=(n-3-sum(len(adj[i]) for i in range(n) if cs[0]>>i&1))%2
  root=find(k)
  if root in parity:assert parity[root]==p
  parity[root]=p
 return {'colorings':len(out),'components':len(parity),'component_parities':list(parity.values()),'counterexample':len(parity)>1 and len(set(parity.values()))==1}
records=[]
for n in [24,30,36]:
 for t in range(40):
  adj,fs=graph(n,2000);r=check(adj,fs);r.update(n=n,sample=t,min_degree=min(map(len,adj)))
  records.append(r);print(r,flush=True)
  if r.get('counterexample'):
   (D/'outputs/parity-witness.json').write_text(json.dumps({'record':r,'adj':[sorted(v) for v in adj]},indent=2));raise SystemExit
(D/'outputs/parity-coverage.json').write_text(json.dumps(records,indent=2)+'\n')
