from fractions import Fraction as F
from pathlib import Path
import itertools,json
D=Path(__file__).resolve().parents[1]
def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def add(a,b,s=1):return [[x+s*y for x,y in zip(u,v)] for u,v in zip(a,b)]
def mul(a,b):return [[sum(x*y for x,y in zip(u,v)) for v in zip(*b)] for u in a]
def tr(a):return list(map(list,zip(*a)))
def inv(a):
 n=len(a);a=[u[:]+v for u,v in zip(a,eye(n))]
 for i in range(n):
  k=next(k for k in range(i,n) if a[k][i]);a[i],a[k]=a[k],a[i]
  x=a[i][i];a[i]=[y/x for y in a[i]]
  for j in range(n):
   if i!=j:
    x=a[j][i]
    if x:a[j]=[y-x*z for y,z in zip(a[j],a[i])]
 return [u[n:] for u in a]
def calc(n,edges,a,check=False):
 d=[sum(i in e for e in edges) for i in range(n)]
 L=[[F(0) for _ in range(n)] for _ in range(n)]
 for i,j in edges:
  L[i][j]=-F(d[i],d[j])**a;L[j][i]=-F(d[j],d[i])**a
 for i in range(n):L[i][i]=-sum(L[i])
 w=[F(x)**(-2*a) for x in d];sw=sum(w);ww=sum(x*x for x in w)
 P=[[w[j]/sw for j in range(n)] for i in range(n)]
 H=add(inv(add(L,P)),P,-1)
 U=[[F(1,n) for j in range(n)] for i in range(n)]
 W=[[w[i]*w[j]/ww for j in range(n)] for i in range(n)]
 M=mul(mul(add(eye(n),U,-1),H),add(eye(n),W,-1))
 if check:
  assert mul(mul(L,M),L)==L and mul(mul(M,L),M)==M
  assert tr(mul(L,M))==mul(L,M) and tr(mul(M,L))==mul(M,L)
  assert mul(mul(L,H),L)==L and mul(mul(H,L),H)==H and mul(L,H)==mul(H,L)
  assert all(sum(w[i]*L[i][j] for i in range(n))==0 for j in range(n))
 mp=sum(M[i][i]+M[j][j]-M[i][j]-M[j][i] for i in range(n) for j in range(i+1,n))
 sp=n*sum(H[i][i] for i in range(n))
 return mp,sp,dict(L=L,MP=M,GI=H,degree=d,left_null=w)
def connected(n,es):
 s={0}
 while True:
  t=s|{j for i,j in es if i in s}|{i for i,j in es if j in s}
  if s==t:return len(s)==n
  s=t
def serial(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):serial(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [serial(v) for v in x]
 return x
witness=list(itertools.combinations(range(6),2))+[(0,6),(6,7),(7,8),(8,9),(9,10)]
r={a:calc(11,witness,a,True) for a in [-1,0,1]}
(D/'outputs/witness-exact.json').write_text(json.dumps(serial(r),indent=2))
print('witness',[(a,str(v[0]),str(v[1])) for a,v in r.items()],flush=True)
# Exhaustive labeled enumeration through n=4, then pendant-clique families through n=11.
counts={};fails=[];equality_failures=[]
for n in range(2,5):
 pairs=list(itertools.combinations(range(n),2));counts[n]=0
 for mask in range(1<<len(pairs)):
  es=[e for k,e in enumerate(pairs) if mask>>k&1]
  if not connected(n,es):continue
  counts[n]+=1;rs={a:calc(n,es,a)[:2] for a in [-1,0,1]}
  for mode in range(2):
   regular=len(set(sum(i in e for e in es) for i in range(n)))==1
   if any((rs[a][mode]==rs[0][mode])!=regular for a in [-1,1]):equality_failures.append((n,es,mode))
   if not rs[-1][mode]<=rs[0][mode]<=rs[1][mode]:fails.append(dict(n=n,edges=es,mode=['MP','spectral'][mode],values=rs))
print('exhaustive',counts,'first',serial(fails[:1]),flush=True)
family=[]
for n in range(3,12):
 for k in range(2,n):
  es=list(itertools.combinations(range(k),2))+[(0,k)]+[(j,j+1) for j in range(k,n-1)]
  rs={a:calc(n,es,a)[:2] for a in [-1,0,1]}
  family.append(dict(n=n,clique=k,values=rs,MP_failure=not rs[-1][0]<=rs[0][0]<=rs[1][0],spectral_failure=not rs[-1][1]<=rs[0][1]<=rs[1][1]))
(D/'outputs/small-search.json').write_text(json.dumps(serial(dict(exhaustive_counts=counts,exhaustive_failures=fails,equality_failures=equality_failures,family=family)),indent=2))
print('family first',[(mode,next((serial(v) for v in family if v[mode+'_failure']),None)) for mode in ['MP','spectral']],flush=True)
