import random,pathlib,json,itertools
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(220)
def check(n,edges):
 adj=[[] for _ in range(n)]
 for a,b in edges:adj[a].append(b);adj[b].append(a)
 d=[]
 for a in range(n):
  ds=[n+1]*n;ds[a]=0;q=[a]
  for x in q:
   for y in adj[x]:
    if ds[y]>n:ds[y]=ds[x]+1;q.append(y)
  d.append(ds)
 if any(x>n for ds in d for x in ds):return 'disconnected'
 diameter=max(max(ds) for ds in d)
 if diameter<=3:return 'known_diameter'
 blocks={};covers={}
 for a,b in itertools.combinations(range(n),2):
  block=cover=0
  for x in range(n):
   if x in (a,b):continue
   if d[a][b]==d[a][x]+d[x][b] or d[a][x]==d[a][b]+d[b][x] or d[b][x]==d[b][a]+d[a][x]:block|=1<<x
   if d[a][x]==d[a][b]+d[b][x] or d[b][x]==d[b][a]+d[a][x]:cover|=1<<x
  blocks[a,b]=block;covers[a,b]=cover
 full=(1<<n)-1
 def rec(S,ban,cover,start):
  if cover==full:return S
  for x in range(start,n):
   if ban>>x&1:continue
   nb=ban;nc=cover|1<<x
   for a in S:nb|=blocks[a,x];nc|=covers[a,x]
   ret=rec(S+[x],nb,nc,x+1)
   if ret is not None:return ret
  return None
 s=rec([],0,0,0)
 if s is None:return {'n':n,'edges':edges}
 return 'terminal_found'
out={}
for n in [12,14,16,18,20]:
 ct={}
 for trial in range(1000):
  edges={(i,(i+1)%n) for i in range(n)};edges={tuple(sorted(e)) for e in edges}
  for i,j in itertools.combinations(range(n),2):
   if rng.random()<rng.choice([0,.02,.05,.10]):edges.add((i,j))
  z=check(n,sorted(edges));key=z if isinstance(z,str) else 'COUNTEREXAMPLE';ct[key]=ct.get(key,0)+1
  if isinstance(z,dict):print(z,flush=True);(L/'outputs/terminal-candidate.json').write_text(json.dumps(z));break
 out[str(n)]=ct;print(n,ct,flush=True);(L/'outputs/terminal-data.json').write_text(json.dumps(out,indent=2))
