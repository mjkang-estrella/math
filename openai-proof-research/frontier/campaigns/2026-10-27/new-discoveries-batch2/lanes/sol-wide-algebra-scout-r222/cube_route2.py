import itertools,json,pathlib,random
L=pathlib.Path(__file__).resolve().parent
rng=random.Random(222)
for n in [5,6,7,8]:
 N=1<<n
 for trial in range(3000):
  p=list(range(n));rng.shuffle(p);t=rng.randrange(N)
  g=[t^sum(((v>>i)&1)<<p[i] for i in range(n)) for v in range(N)]
  seen=set();cycles=[]
  for v in range(N):
   if v in seen:continue
   c=[];w=v
   while w not in seen:seen.add(w);c.append(w);w=g[w]
   cycles.append(c)
  eligible=[c for c in cycles if len(c)>2]
  if not eligible:continue
  special=rng.choice(eligible);k=rng.randrange(1,len(special))
  x=set(special[:k])
  for c in cycles:
   if c!=special and rng.randrange(2):x.update(c)
  y={g[v] for v in x};z=x|y;a=next(iter(z-x));b=next(iter(z-y))
  def signature(v):
   return sorted(((v^w).bit_count(),tuple(sorted((w^u).bit_count() for u in z))) for w in z)
  if signature(a)!=signature(b):
   result=dict(n=n,trial=trial,z=sorted(z),x=sorted(x),y=sorted(y),a=a,b=b,coordinate_permutation=p,translation=t,signature_a=signature(a),signature_b=signature(b))
   (L/'cube-route2-result.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if not k.startswith('signature')}));raise SystemExit
 print('no signature obstruction',n)
