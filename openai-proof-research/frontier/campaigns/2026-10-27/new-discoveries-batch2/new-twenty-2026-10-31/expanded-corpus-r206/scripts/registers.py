import itertools,collections,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
def distances(n):
 N=1<<n;gens=[]
 for i in range(n):
  pairs=[(x,x^(1<<i)) for x in range(N) if not(x>>i&1)]
  for mask in range(1,1<<len(pairs)):
   p=list(range(N))
   for j,(a,b) in enumerate(pairs):
    if mask>>j&1:p[a],p[b]=p[b],p[a]
   gens.append(p)
 init=tuple(range(N));ds={init:0};q=collections.deque([init])
 while q:
  p=q.popleft();d=ds[p]+1
  for g in gens:
   h=tuple(g[v] for v in p)
   if h not in ds:ds[h]=d;q.append(h)
 return ds
small=distances(1);mid=distances(2);big=distances(3);bad=[];cases=0
for k in [1,2]:
 dl,dr=(small,mid) if k==1 else (mid,small)
 for g in dl:
  for h in dr:
   f=tuple(g[x&((1<<k)-1)]|(h[x>>k]<<k) for x in range(8));cases+=1
   if big[f]!=dl[g]+dr[h]:bad.append({'k':k,'g':g,'h':h})
r={'alphabet_size':2,'registers':3,'Cayley_states':len(big),'block_splits':[1,2],'independent_products_checked':cases,'counterexamples':bad,'distance_histogram':dict(collections.Counter(big.values()))};print(json.dumps(r));(D/'outputs/registers-binary3.json').write_text(json.dumps(r,indent=2))
