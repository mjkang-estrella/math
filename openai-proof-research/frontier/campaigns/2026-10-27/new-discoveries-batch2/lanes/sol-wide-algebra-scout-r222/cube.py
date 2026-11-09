import itertools,json,pathlib
L=pathlib.Path(__file__).resolve().parent
n=4; N=1<<n
perms=[]
for p in itertools.permutations(range(n)):
 for a in range(N):
  perms.append(tuple(a^sum(((v>>i)&1)<<p[i] for i in range(n)) for v in range(N)))
def act(z,p):
 out=0
 while z:
  t=z&-z;z-=t;out|=1<<p[t.bit_length()-1]
 return out
gens=[tuple(v^(1<<i) for v in range(N)) for i in range(n)]+[tuple(sum(((v>>j)&1)<<(i+1 if j==i else i if j==i+1 else j) for j in range(n)) for v in range(N)) for i in range(n-1)]
orb=[-1]*(1<<N); reps=[]
for z in range(1<<N):
 if orb[z]>=0:continue
 orb[z]=z;reps.append(z);todo=[z]
 for w in todo:
  for p in gens:
   u=act(w,p)
   if orb[u]<0:orb[u]=z;todo.append(u)
for z in sorted(reps,key=lambda z:(z.bit_count(),z)):
 verts=[v for v in range(N) if z>>v&1];stab=[p for p in perms if act(z,p)==z]
 for a,b in itertools.combinations(verts,2):
  x=z^(1<<a);y=z^(1<<b)
  if orb[x]==orb[y] and not any(p[a]==b for p in stab):
   g=next(p for p in perms if act(x,p)==y)
   result=dict(n=n,z=verts,a=a,b=b,x=[v for v in verts if v!=a],y=[v for v in verts if v!=b],g=g,stabilizer=stab,orbits=len(reps),group=len(perms),distance_profiles={str(v):sorted((v^w).bit_count() for w in verts if w!=v) for v in [a,b]})
   (L/'cube-result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result));raise SystemExit
print('no counterexample')
