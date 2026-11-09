import pathlib,itertools,json,math
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1]
def connected(n,es):
 seen={0}
 while True:
  old=len(seen)
  for a,b in es:
   if a in seen or b in seen:seen.update((a,b))
  if len(seen)==old:return len(seen)==n
def poly(n,es):
 p=[0]*(n+1)
 for mask in range(1<<len(es)):
  par=list(range(n))
  def root(a):
   while par[a]!=a:a=par[a]
   return a
  for j,(a,b) in enumerate(es):
   if mask>>j&1:par[root(a)]=root(b)
  p[len({root(a) for a in range(n)})]+=(-1)**mask.bit_count()
 return p
out=[]
for n in range(3,7):
 pairs=list(itertools.combinations(range(n),2));idx={e:i for i,e in enumerate(pairs)};seen=set();rows=[]
 for mask in range(1<<len(pairs)):
  if mask in seen:continue
  es=[e for i,e in enumerate(pairs) if mask>>i&1]
  for perm in itertools.permutations(range(n)):
   code=sum(1<<idx[tuple(sorted((perm[a],perm[b])))] for a,b in es);seen.add(code)
  if not connected(n,es):continue
  p=poly(n,es);fails=[]
  for x in [-1,-2,-10]:
   q=[sum(p[i]*math.comb(i,j)*x**(i-j) for i in range(j,n+1))*(-1)**n for j in range(n+1)]+[0]*30
   l=[F(0)]*31
   for k in range(1,31):
    l[k]=(F(k*q[k])-sum(i*l[i]*q[k-i] for i in range(1,k)))/(k*q[0])
    if k>=2 and l[k]>=0:fails.append(dict(x=x,k=k,coefficient=str(l[k])))
  # facets normalized potential enumeration; breadth first radius bounds
  dist={0:0}
  for _ in range(n):
   for a,b in es:
    if a in dist:dist[b]=min(dist.get(b,n),dist[a]+1)
    if b in dist:dist[a]=min(dist.get(a,n),dist[b]+1)
  count=0
  for v in itertools.product(*(range(-dist[i],dist[i]+1) for i in range(1,n))):
   f=(0,)+v
   if any(abs(f[a]-f[b])>1 for a,b in es):continue
   count+=connected(n,[(a,b) for a,b in es if abs(f[a]-f[b])==1])
  rows.append(dict(mask=mask,edges=es,chromatic_polynomial_ascending=p,derivative_failures=fails,facets=count))
 lo=3*2**((n-1)//2)-2 if n%2 else 2**(n//2+1)-2
 hi=6**((n-1)//2) if n%2 else 14*6**(n//2-2)
 out.append(dict(n=n,connected_isomorphism_classes=len(rows),lower=lo,upper=hi,rows=rows,facet_failures=[x for x in rows if not lo<=x['facets']<=hi]))
 (D/'outputs/graphs.json').write_text(json.dumps(out,indent=2)+'\n');print(n,len(rows),len(out[-1]['facet_failures']),sum(len(x['derivative_failures']) for x in rows),flush=True)
