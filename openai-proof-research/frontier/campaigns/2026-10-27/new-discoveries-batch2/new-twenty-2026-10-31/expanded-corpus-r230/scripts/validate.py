import pathlib,itertools,json
D=pathlib.Path(__file__).resolve().parents[1]
src=(D/'scripts/fence.py').read_text().split('N,lo,hi=')[0];exec(compile(src,str(D/'scripts/fence.py'),'exec'))
checks=0
for n in range(1,7):
 for w in range(1<<max(0,n-1)):
  for m in (1,2,3):
   a=[0]*(n*m+1)
   for xs in itertools.product(range(m+1),repeat=n):
    if all((xs[i+1]<=xs[i] if (w>>i)&1 else xs[i+1]>=xs[i]) for i in range(n-1)):a[sum(xs)]+=1
   assert a==poly(n,m,w),(n,m,w)
   checks+=1
# Direct enumeration of the four-vertex family and all pairs.
es=list(itertools.combinations(range(4),2));family=[h for h in range(64) if h.bit_count()>=4]
for a in family:
 for b in family:
  par=list(range(4))
  def root(x):
   while par[x]!=x:x=par[x]
   return x
  for j,(u,v) in enumerate(es):
   if (a&b)>>j&1:par[root(u)]=root(v)
  assert len({root(i) for i in range(4)})<=2
assert len(family)==22
print(json.dumps(dict(fence_bruteforce_instances=checks,family_size=len(family),ordered_pairs=len(family)**2,conclusion='diagnostic algorithms cross-checked; no formal theorem claimed')),flush=True)
