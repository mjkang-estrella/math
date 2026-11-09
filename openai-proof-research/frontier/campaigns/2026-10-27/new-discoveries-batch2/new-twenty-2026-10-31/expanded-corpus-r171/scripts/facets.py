import pathlib,itertools,json,collections
D=pathlib.Path(__file__).resolve().parents[1]
def connected(n,edges):
 seen={0}
 while True:
  old=len(seen)
  for a,b in edges:
   if a in seen or b in seen:seen.update((a,b))
  if len(seen)==old:return len(seen)==n
out=[]
for n in range(3,6):
 rows=[];pairs=list(itertools.combinations(range(n),2))
 for mask in range(1<<len(pairs)):
  edges=[e for i,e in enumerate(pairs) if mask>>i&1]
  if not connected(n,edges):continue
  dist={0:0}
  for _ in range(n):
   for a,b in edges:
    if a in dist:dist[b]=min(dist.get(b,n),dist[a]+1)
    if b in dist:dist[a]=min(dist.get(a,n),dist[b]+1)
  count=0
  for v in itertools.product(*(range(-dist[i],dist[i]+1) for i in range(1,n))):
   f=(0,)+v
   if any(abs(f[a]-f[b])>1 for a,b in edges):continue
   if connected(n,[(a,b) for a,b in edges if abs(f[a]-f[b])==1]):count+=1
  rows.append(dict(mask=mask,facets=count))
 lower=3*2**((n-1)//2)-2 if n%2 else 2**(n//2+1)-2
 upper=6**((n-1)//2) if n%2 else 14*6**(n//2-2)
 out.append(dict(n=n,graphs=len(rows),lower=lower,upper=upper,failures=[x for x in rows if not lower<=x['facets']<=upper],rows=rows))
(D/'outputs/facets.json').write_text(json.dumps(out,indent=2)+'\n');print([(o['n'],o['graphs'],o['failures']) for o in out])
