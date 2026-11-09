import json,itertools,pathlib,collections
L=pathlib.Path(__file__).resolve().parent
r=json.loads((L/'cube-route2-result.json').read_text());n=r['n'];p=r['coordinate_permutation'];t=r['translation'];N=1<<n
g=[t^sum(((v>>i)&1)<<p[i] for i in range(n)) for v in range(N)]
cycles=[];seen=set()
for v in range(N):
 if v in seen:continue
 c=[];w=v
 while w not in seen:seen.add(w);c.append(w);w=g[w]
 cycles.append(c)
def sig(z,v):
 return sorted(((v^w).bit_count(),tuple(sorted((w^u).bit_count() for u in z))) for w in z)
best=None
for ci,c in enumerate(cycles):
 if len(c)<3:continue
 others=[d for j,d in enumerate(cycles) if j!=ci]
 for start in range(len(c)):
  for k in range(1,len(c)):
   partial={c[(start+i)%len(c)] for i in range(k)}
   for bits in range(1<<len(others)):
    x=partial|set(v for i,d in enumerate(others) if bits>>i&1 for v in d);y={g[v] for v in x};z=x|y
    if best and len(z)>=len(best['z']):continue
    a=next(iter(z-x));b=next(iter(z-y))
    if sig(z,a)!=sig(z,b):best=dict(z=sorted(z),a=a,b=b,x=sorted(x),y=sorted(y),p=p,t=t,n=n)
assert best
z=best['z'];a=best['a'];b=best['b']
best['profiles']={str(v):[sum((v^u).bit_count()==d for u in z) for d in range(n+1)] for v in z}
best['signatures']={str(v):collections.Counter(str(((v^w).bit_count(),best['profiles'][str(w)])) for w in z) for v in [a,b]}
(L/'cube-certificate.json').write_text(json.dumps(best,indent=2));print(json.dumps(best,indent=2))
