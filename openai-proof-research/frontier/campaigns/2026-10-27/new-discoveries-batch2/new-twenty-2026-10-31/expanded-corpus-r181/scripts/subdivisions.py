from pathlib import Path
from itertools import combinations,product,combinations_with_replacement
import json,collections
D=Path(__file__).resolve().parents[1]
def invariants(adj):
 n=len(adj);dist=[]
 for v in range(n):
  d=[999]*n;d[v]=0;queue=[v]
  for u in queue:
   for w in adj[u]:
    if d[w]==999:d[w]=d[u]+1;queue.append(w)
  dist.append(d)
 edges=[(v,w) for v in range(n) for w in adj[v] if v<w]
 def md(edge):
  rows=[[min(d[u],d[v]) for u,v in edges] if edge else d for d in dist]
  universe=list(combinations(range(len(rows[0])),2));covers=[sum(1<<j for j,(a,b) in enumerate(universe) if row[a]!=row[b]) for row in rows];full=(1<<len(universe))-1
  for k in range(1,min(n,6)+1):
   for s in combinations(range(n),k):
    hit=0
    for v in s:hit|=covers[v]
    if hit==full:return k
  return None
 vd,ed=md(False),md(True)
 # A witnessed forcing set suffices for upper Z, but comparison needs lower Z.
 # Compute exact Z in increasing cardinality.
 bits=[sum(1<<w for w in a) for a in adj];full=(1<<n)-1
 for k in range(1,n+1):
  found=False
  for s in combinations(range(n),k):
   mask=sum(1<<v for v in s);old=-1
   while mask!=old:
    old=mask
    for v in range(n):
     if mask>>v&1:
      rem=bits[v]&~mask
      if rem and rem&(rem-1)==0:mask|=rem
   if mask==full:found=True;break
  if found:Z=k;break
 return vd,ed,Z
out=[]
for kind in ['theta','K4']:
 rows=[]; hist=collections.Counter()
 lens=combinations_with_replacement(range(1,9),3) if kind=='theta' else product(range(1,4),repeat=6)
 for lengths in lens:
  if kind=='theta' and lengths.count(1)>1:continue
  core=[(0,1)]*3 if kind=='theta' else list(combinations(range(4),2));adj=[set() for _ in range(2 if kind=='theta' else 4)]
  for (a,b),length in zip(core,lengths):
   last=a
   for _ in range(length-1):
    v=len(adj);adj.append({last});adj[last].add(v);last=v
   adj[last].add(b);adj[b].add(last)
  vd,ed,Z=invariants(adj);c=len(core)-(2 if kind=='theta' else 4)+1
  rows.append({'lengths':lengths,'n':len(adj),'dim':vd,'edim':ed,'Z':Z,'c':c});hist[(vd,ed,Z)]+=1
  if vd is None or ed is None or vd>2*c or ed>Z+c:print('FAIL',kind,rows[-1],flush=True)
 print(kind,'count',len(rows),'histogram',sorted(hist.items()),flush=True)
 out.append({'family':kind,'rows':rows})
(D/'outputs/subdivisions.json').write_text(json.dumps(out,indent=2))
