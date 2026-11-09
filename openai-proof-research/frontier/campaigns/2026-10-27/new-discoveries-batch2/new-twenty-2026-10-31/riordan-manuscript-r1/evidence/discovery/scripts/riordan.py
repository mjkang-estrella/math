import pathlib,json,sys
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1]
def mul(a,b,n):
 c=0
 while b:
  if b&1:c^=a
  a<<=1;b>>=1
 return c&((1<<n)-1)
def mat(n,mask):
 g=[1]*n
 for k in range(1,n):g[k]=g[k//2] if k%2 else (mask>>(k//2-1))&1
 gb=sum(v<<i for i,v in enumerate(g));p=gb;A=[[0]*n for _ in range(n)]
 for j in range(n-1):
  for i in range(j+1,n):A[i][j]=A[j][i]=(p>>(i-j-1))&1
  p=mul(p,gb,n)
 return A,g
def rank(A,p=1000003):
 a=[list(map(Fraction,r)) if p is None else r[:] for r in A];m=len(a);n=len(a[0]);k=0
 for j in range(n):
  pivot=next((i for i in range(k,m) if a[i][j]),None)
  if pivot is None:continue
  a[k],a[pivot]=a[pivot],a[k];inv=1/a[k][j] if p is None else pow(a[k][j],-1,p)
  for i in range(k+1,m):
   if not a[i][j]:continue
   v=a[i][j]*inv
   if p is None:a[i][j:]=[x-v*y for x,y in zip(a[i][j:],a[k][j:])]
   else:a[i][j:]=[(x-v*y)%p for x,y in zip(a[i][j:],a[k][j:])]
  k+=1
  if k==m:break
 return k
lo,hi=map(int,sys.argv[1:]);total=0
for n in range(lo,hi+1):
 count=0;sing=0
 for mask in range(1<<max(0,(n-2)//2)):
  A,g=mat(n,mask);c=(n+1)//2;B=[r[1::2] for r in A[::2]]
  assert all(not any(r[1::2]) for r in A[1::2])
  small=mat(c,mask)[0];assert [r[::2] for r in A[::2]]==small
  ra=rank(A);rb=rank(B)
  if ra<n:sing+=1
  if ra!=c+rb:
   qa=rank(A,None);qb=rank(B,None)
   if qa!=c+qb:
    out={'n':n,'mask':mask,'g':g,'A':A,'rank_Q':qa,'rank_B_Q':qb}
    (D/'outputs/riordan-witness.json').write_text(json.dumps(out,indent=2)+'\n');print('WITNESS',out,flush=True);sys.exit()
  count+=1
 print({'n':n,'g_prefixes':count,'modular_singular':sing,'counterexample':False,'caveat':'non-findings modular only; exceptions verified over Q'},flush=True)
