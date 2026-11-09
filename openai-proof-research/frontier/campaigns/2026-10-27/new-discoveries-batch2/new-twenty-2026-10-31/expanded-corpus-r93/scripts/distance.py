import itertools,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];res=[]
for n in range(1,6):
 es=list(itertools.combinations(range(n),2));regular=0;strong=0;dt=0
 for cs in itertools.product(range(3),repeat=len(es)):
  rows=[0]*n;ind=[0]*n
  for c,(a,b) in zip(cs,es):
   if c==1:rows[a]|=1<<b;ind[b]+=1
   if c==2:rows[b]|=1<<a;ind[a]+=1
  k=rows[0].bit_count()
  if any(r.bit_count()!=k for r in rows) or any(x!=k for x in ind):continue
  regular+=1;dist=[]
  for v in range(n):
   ds=[-1]*n;ds[v]=0;todo=[v]
   for a in todo:
    for b in range(n):
     if rows[a]>>b&1 and ds[b]<0:ds[b]=ds[a]+1;todo.append(b)
   dist.append(ds)
  if any(-1 in ds for ds in dist):continue
  strong+=1
  autos=[]
  for p in itertools.permutations(range(n)):
   if all(rows[p[a]]==sum(((rows[a]>>b)&1)<<p[b] for b in range(n)) for a in range(n)):autos.append(p)
  if len({p[0] for p in autos})!=n:continue
  good=True
  for d in set(dist[0]):
   pairs={(a,b) for a in range(n) for b in range(n) if dist[a][b]==d};a,b=next(iter(pairs))
   if {(p[a],p[b]) for p in autos}!=pairs:good=False;break
  if good:
   dt+=1
   sec=set()
   for a in range(n):
    if rows[0]>>a&1:sec.update(b for b in range(n) if rows[a]>>b&1)
   sec-={0};sec-={b for b in range(n) if rows[0]>>b&1}
   if len(sec)!=k:print('WITNESS',n,rows,k,len(sec),flush=True)
 print('COMPLETE',n,3**len(es),regular,strong,dt,flush=True);res.append([n,3**len(es),regular,strong,dt]);(D/'outputs/distance.json').write_text(json.dumps(res))
