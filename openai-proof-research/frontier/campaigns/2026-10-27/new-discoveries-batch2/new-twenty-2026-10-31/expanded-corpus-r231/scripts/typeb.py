import pathlib,itertools,json,time,sys
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);roots=[];domains=[]
for i in range(n):
 v=[0]*n;v[i]=1;roots.append(tuple(v));domains.append(sum(1<<k for k in range(i,n)))
for i in range(n):
 for j in range(i+1,n):
  for sign in [-1,1]:
   v=[0]*n;v[i]=1;v[j]=sign;roots.append(tuple(v));domains.append(sum(1<<k for k in range(i,j if sign==-1 else n)))
for i in range(n):
 v=[0]*n;v[i]=1
 if i<n-1:v[i+1]=-1
 domains[roots.index(tuple(v))]=1<<i
constraints=[]
for a,b in itertools.combinations(range(len(roots)),2):
 u,v=roots[a],roots[b];ij=next(((i,j) for i in range(n) for j in range(i+1,n) if u[i]*v[j]-u[j]*v[i]),None)
 if ij is None:continue
 i,j=ij;det=u[i]*v[j]-u[j]*v[i]
 for c,w in enumerate(roots):
  if c in (a,b):continue
  x=w[i]*v[j]-w[j]*v[i];y=u[i]*w[j]-u[j]*w[i]
  if x*det<=0 or y*det<=0:continue
  if all(x*u[k]+y*v[k]==det*w[k] for k in range(n)):constraints.append((a,b,c))
start=time.monotonic();count=nodes=0;stopped=False
# Rank-two closure tests are used as a diagnostic, not asserted formally equivalent here.
def dfs(ds):
 global count,nodes,stopped
 nodes+=1
 if nodes%1000==0 and time.monotonic()-start>100:stopped=True;return
 change=True
 while change:
  change=False
  for a,b,c in constraints:
   da,db,dc=ds[a],ds[b],ds[c]
   nc=dc&(da|db)
   na=da if dc&db else da&dc
   nb=db if dc&da else db&dc
   if not na or not nb or not nc:return
   if (na,nb,nc)!=(da,db,dc):ds[a],ds[b],ds[c]=na,nb,nc;change=True
 sizes=[(x.bit_count(),i) for i,x in enumerate(ds) if x.bit_count()>1]
 if not sizes:count+=1;return
 _,i=min(sizes);opts=ds[i]
 while opts:
  b=opts&-opts;opts-=b;new=ds.copy();new[i]=b;dfs(new)
  if stopped:return
from math import comb
expected=sum(__import__('fractions').Fraction(3*k+1,n+k+1)*(comb(2*n-k,n-2*k) if n-2*k>=0 else 0) for k in range(n+1))
dfs(domains)
res=dict(n=n,positive_roots=len(roots),rank_two_constraints=len(constraints),assignments=count,conjectured_count=str(expected),nodes=nodes,complete=not stopped,wall=time.monotonic()-start,semantic_limit='Rank-two closure and simple-root rainbow reduction require proof before using a disagreement as an exact refutation')
print(res);(D/f'typeb-{n}.json').write_text(json.dumps(res,indent=2)+'\n')
