import pathlib,json,random,functools,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(221);start=time.monotonic()
def sample(N):
 ms=[];used=set()
 for c in range(3):
  for attempt in range(100):
   p=list(range(N));rng.shuffle(p);m=[tuple(sorted(p[i:i+2])) for i in range(0,N,2)]
   if not any(e in used for e in m):break
  else:return None
  used.update(m);ms.append(m)
 return ms
def run(ms,N):
 adj=[[] for _ in range(N)]
 for c,es in enumerate(ms):
  for a,b in es:adj[a].append((b,c));adj[b].append((a,c))
 reach={0};q=[0]
 for x in q:
  for y,c in adj[x]:
   if y not in reach:reach.add(y);q.append(y)
 if len(reach)<N:return None
 n=N//2;B=n+1
 @functools.lru_cache(None)
 def solve(s,u):
  if not s:return {0} if u==0 else set()
  x=(s&-s).bit_length()-1;s^=1<<x;ans=set()
  if u:ans.update(solve(s,u-1))
  for y,c in adj[x]:
   if s>>y&1:ans.update(z+B**c for z in solve(s^(1<<y),u))
  return ans
 got=solve((1<<N)-1,2)
 missing=[(a,b,n-1-a-b) for a in range(n) for b in range(n-a) if a+B*b+B*B*(n-1-a-b) not in got]
 return missing
stats={};hit=None
for N in [8,10,12,14,16,18,20,22,24]:
 count=connected=0;t=time.monotonic()
 for _ in range(2000):
  if time.monotonic()-t>10:break
  count+=1;ms=sample(N)
  if not ms:continue
  bad=run(ms,N)
  if bad is None:continue
  connected+=1
  if bad:hit={'N':N,'matchings':ms,'missing':bad};break
 stats[str(N)]={'random_samples':count,'connected_simple_graphs_checked':connected,'seconds':time.monotonic()-t};print(N,stats[str(N)],flush=True)
 if hit:print('HIT',hit,flush=True);break
(D/'outputs/matching-search.json').write_text(json.dumps({'seed':221,'stats':stats,'hit':hit,'scope':'independent uniform shuffled disjoint perfect matchings; only connected simple unions tested; not an isomorph-free enumeration'},indent=2))
