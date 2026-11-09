import pathlib,json,itertools,collections,time,sys,math
D=pathlib.Path(__file__).resolve().parents[1]
mode=sys.argv[1]
def save(name,o):
 (D/f'outputs/{name}.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o),flush=True)
if mode=='semigroups':
 level=[frozenset()];rows=[]
 for g in range(21):
  counts=collections.Counter();new=[]
  for gaps in level:
   F=max(gaps,default=-1);m=next(i for i in range(1,F+3) if i not in gaps)
   typ=sum(all(y-x in gaps for y in gaps if y>x) for x in gaps);counts[typ]+=1
   if g<20:
    for x in range(max(F+1,m),F+m+2):
     if x in gaps:continue
     if all(y in gaps or x-y in gaps for y in range(1,x//2+1)):new.append(gaps|{x})
  assert len(set(level))==len(level)
  rows.append({'genus':g,'total':len(level),'counts':dict(counts)})
  save('semigroups',rows)
  level=new
if mode=='polynomials':
 import sympy as s
 from sympy.utilities.iterables import partitions
 x=s.Symbol('x'); rows=[]
 start=int(sys.argv[2]);end=int(sys.argv[3])
 for n in range(start,end+1):
  parts=list(partitions(n)); polys=[]
  for p in parts:
   f=s.Poly(1,x,domain=s.ZZ)
   for i,m in p.items():f*=s.Poly(1+x**i,x)**m
   polys.append(f)
  den=s.Poly(1,x,domain=s.ZZ)
  for f in polys:den=s.lcm(den,f)
  num=sum((den.exquo(f) for f in polys),s.Poly(0,x,domain=s.ZZ))
  fac=s.factor_list(num)
  rows.append({'n':n,'partitions':len(parts),'degree':num.degree(),'coefficients_descending':[int(v) for v in num.all_coeffs()],'factorization':str(fac),'irreducible':num.is_irreducible})
  save(f'polynomials-{start}-{end}',rows)
if mode=='congruence':
 N=2000;a=[[0]*(N+1) for _ in range(4)];a[0][0]=1
 for i in range(1,N+1):
  for j in range(3,0,-1):
   acc=[0]*(N+1)
   for v in range(i,N+1):acc[v]=a[j-1][v-i]+acc[v-i];a[j][v]+=acc[v]
 rows=[{'n':n,'argument':36*n+30,'nu2':a[2][36*n+30],'nu3':a[3][36*n+30]} for n in range((N-30)//36+1)]
 save('congruence',{'range':N,'rows':rows,'failures':[r for r in rows if r['nu2']%4 or r['nu3']%2]})
if mode=='curling':
 def curl(s):
  n=len(s);best=1
  for l in range(1,n//2+1):
   block=s[-l:];k=1
   while (k+1)*l<=n and s[-(k+1)*l:-k*l]==block:k+=1
   best=max(best,k)
  return best
 def tail(s):
  s=list(s);start=len(s)
  for t in range(500):
   k=curl(s)
   if k==1:return len(s)-start
   s.append(k)
  return None
 rows=[]
 for n in range(1,13):
  count=0;unknown=0;found=[]
  for s in itertools.product([2,3],repeat=n):
   t=tail(s);a=tail((2,)+s);b=tail((3,)+s);count+=1
   if None in [t,a,b]:unknown+=1
   elif a<t and b<t:found.append(s)
  rows.append({'length':n,'all_words':count,'tail_cap':500,'unresolved':unknown,'witnesses':found});save('curling',rows)
if mode=='stack':
 from functools import lru_cache
 h=int(sys.argv[2]);n=2**(h+1)-1
 adj=[[] for _ in range(n)]
 for v in range(1,n):adj[v].append((v-1)//2);adj[(v-1)//2].append(v)
 dist=[]
 for v in range(n):
  d=[999]*n;d[v]=0;q=[v]
  for u in q:
   for w in adj[u]:
    if d[w]>d[u]+1:d[w]=d[u]+1;q.append(w)
  dist.append(d)
 rows=[]
 for depth in range(h+1):
  r=2**depth-1;states=[0];limit=200000
  @lru_cache(None)
  def solve(c):
   states[0]+=1
   if states[0]>limit:raise RuntimeError('state cap')
   if c[r]==n:return ()
   if any(c[u]>max(dist[u]) for u in range(n) if u!=r):return None
   moves=[(u,v) for u in range(n) if c[u] and u!=r for v in range(n) if u!=v and c[v] and c[u]==dist[u][v]]
   moves.sort(key=lambda uv:(uv[1]!=r,-c[uv[0]]))
   for u,v in moves:
    a=list(c);a[v]+=a[u];a[u]=0;ans=solve(tuple(a))
    if ans is not None:return ((u,v),)+ans
   return None
  try:ans=solve((1,)*n);status='stackable' if ans is not None else 'not stackable'
  except RuntimeError:ans=None;status='state cap'
  rows.append({'height':h,'n':n,'target':r,'depth':depth,'status':status,'states':states[0],'moves':ans});save(f'stack-{h}',rows)
