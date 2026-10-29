import json,sys,math
from pathlib import Path
P=Path(__file__).parent

def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 return c

def mul(a,b,L=9):
 c=[0]*min(L,len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b[:max(0,L-i)]):c[i+j]+=x*y
 return c

def mm(A,B,L=9):return [[add(mul(A[i][0],B[0][j],L),mul(A[i][1],B[1][j],L)) for j in range(2)] for i in range(2)]
def matpow(A,k,L=9):
 R=[[[1],[0]],[[0],[1]]]
 for _ in range(k):R=mm(A,R,L)
 return R

def cycle(n):
 if n==1:return [(0,-1,[1,1]),(0,1,[1,1]),(1,-1,[1,1,-1])]
 T=add([0]+[1]*n,mul(add([1],[0]*n+[1]),[1,-1],n+3))
 v2=(n-1,-1,add(T,[0]*(n+1)+[1]));v3=(0,1,[1]);v0=(n-1,1,add(T,[0]*(n+1)+[1]));v1=(n,-1,T)
 W=[]
 for i in range(n-2):W += [(n-i-2,-1,add([1]*(n-i),[0,-1])),(i,-1,[1]*(i+2)),(1,-1,[1,1,-1])]
 W += [(0,-1,add([1,1],[0,-1]))]
 for i in range(n-1):W += [(n-i-2,-1,[1]*(n-i)),(i,-1,add([1]*(i+2),[0,-1])),(0,-1,[1] if i==n-2 else [1,-1])]
 return [v2,v3]+W+[v0,v1]

def coeff(n,L):
 # q*F^2+B*F=1, B=(1+q^n)(1-q)-q[n]_q
 B=add(mul(add([1],[0]*n+[1]),[1,-1],n+3),[0]+[-1]*n)
 f=[1]
 for r in range(1,L):f.append(-sum(f[i]*f[r-1-i] for i in range(r))-sum(B[i]*f[r-i] for i in range(1,min(r,len(B)-1)+1)))
 return f

def det(a):
 if not a:return 1
 a=[r[:] for r in a];d=1;s=1;N=len(a)
 for k in range(N-1):
  if not a[k][k]:
   pivot=next((i for i in range(k+1,N) if a[i][k]),None)
   if pivot is None:return 0
   a[k],a[pivot]=a[pivot],a[k];s=-s
  p=a[k][k]
  for i in range(k+1,N):
   for j in range(k+1,N):
    v=a[i][j]*p-a[i][k]*a[k][j]
    assert v%d==0
    a[i][j]=v//d
   a[i][k]=0
  d=p
 return s*a[-1][-1]

def diffs(a):return [y-x for x,y in zip(a,a[1:])]
mode=sys.argv[1] if len(sys.argv)>1 else 'transfer'
if mode=='transfer':
 rows=[]
 for n in range(1,17):
  M=[[[1],[0]],[[0],[1]]]
  for k,v,D in cycle(n):
   assert all(x==0 for x in D[k+2:])
   a=(D+[0]*(k+2-len(D)))[:k+2][::-1]
   M=mm([[a,[-v]],[[1],[0]]],M)
  assert [[M[i][j][0] for j in range(2)] for i in range(2)]==[[1,0],[0,1]]
  for d in range(7):
   seq=[(matpow(M,k)[0][0]+[0]*9)[d] for k in range(12)]
   for _ in range(d+1):seq=diffs(seq)
   assert not any(seq)
  rows.append({'n':n,'steps':len(cycle(n)),'degree_weight':sum(k+1 for k,v,D in cycle(n)),'monodromy':M})
 out={'status':'PASS','scope':'finite exact transfer identities and seven jet degrees, not source proof','rows':rows}
else:
 n=int(sys.argv[2]);maxj=int(sys.argv[3]);shifts=list(range(n+2,n+7));rho=2*n*(n+1)*(2 if n%2 else 1)
 f=coeff(n,2*maxj+max(shifts)+1);rows=[]
 for ell in shifts:
  ds=[det([[f[ell+i+j] for j in range(m)] for i in range(m)]) for m in range(maxj+1)]
  profiles=[]
  for r in range(rho):
   seq=ds[r::rho];cur=seq[:];degree=0
   while len(cur)>1 and any(cur):cur=diffs(cur);degree+=1
   # Saturated finite interpolation cannot certify a degree. Record raw differences.
   profiles.append({'r':r,'samples':seq,'first_zero_difference_order':degree if len(cur)>1 else None,'last_differences':cur})
  rows.append({'shift':ell,'values':ds,'profiles':profiles})
 out={'status':'PASS','n':n,'max_size':maxj,'rho':rho,'scope':'finite exact determinants; no universal interpolation inference','rows':rows}
(P/('checks-'+mode+('' if mode=='transfer' else '-'+str(n))+'.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','mode':mode,'rows':len(rows)}))
