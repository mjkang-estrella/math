import pathlib,itertools,json,resource,os,time
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));D=pathlib.Path(__file__).resolve().parents[1]
# F_27 = F_3[z]/(z^3-z-1); this cubic has no F3 roots.
V=list(itertools.product(range(3),repeat=3));idx={v:i for i,v in enumerate(V)}
def add(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def mul(a,b):
 c=[0]*5
 for i in range(3):
  for j in range(3):c[i+j]+=a[i]*b[j]
 for i in [4,3]:c[i-3]+=c[i];c[i-2]+=c[i]
 return tuple(x%3 for x in c[:3])
squares={mul(v,v) for v in V[1:]};assert len(squares)==13
rows=[];count=0;cliques=0;bad=[]
# Every 3-subspace of F3^6 has one RREF generator. Check all, not only graphs y=f(x).
for piv in itertools.combinations(range(6),3):
 free=[(r,c) for r in range(3) for c in range(6) if c not in piv and c>piv[r]]
 for vals in itertools.product(range(3),repeat=len(free)):
  a=[[int(c==piv[r]) for c in range(6)] for r in range(3)]
  for (r,c),v in zip(free,vals):a[r][c]=v
  count+=1;kind=None;valid=True
  for coeff in itertools.product(range(3),repeat=3):
   if not any(coeff):continue
   z=tuple(sum(coeff[r]*a[r][c] for r in range(3))%3 for c in range(6));quad=add(mul(z[:3],z[:3]),mul(z[3:],z[3:]));k=quad in squares
   if kind is None:kind=k
   elif kind!=k:valid=False;break
  if valid:
   cliques+=1
   points=[tuple(sum(coeff[r]*a[r][c] for r in range(3))%3 for c in range(6)) for coeff in itertools.product(range(3),repeat=3)]
   u=next(z for z in points if any(z));line={mul(s,u[:3])+mul(s,u[3:]) for s in V}
   if set(points)!=line:bad.append({'basis':a,'complete':kind,'points':points})
print(json.dumps({'id':379296,'field':'F3[z]/(z^3-z-1)','space':'all 3-dimensional F3-linear subspaces of F27^2, based at zero; affine translates follow by invariance; excludes nonlinear sets','subspaces':count,'homogeneous_subspaces':cliques,'nonline_counterexamples':bad},indent=2))
