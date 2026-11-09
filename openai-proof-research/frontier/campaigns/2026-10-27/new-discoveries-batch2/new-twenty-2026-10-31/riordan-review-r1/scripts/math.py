from fractions import Fraction as F
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
def matrix(g,n):
 powers=[[1]+[0]*(n-1)]
 for k in range(n): powers.append([sum(g[t]*powers[-1][r-t] for t in range(r+1)) for r in range(n)])
 B=[[0 if i<=j else powers[j+1][i-j-1]%2 for j in range(n)] for i in range(n)]
 return B,[[B[i][j]+B[j][i] for j in range(n)] for i in range(n)]
def ker(a):
 m=[list(map(F,r)) for r in a]; nr=len(m);nc=len(m[0]); piv=[]
 for c in range(nc):
  r=next((r for r in range(len(piv),nr) if m[r][c]),None)
  if r is None:continue
  k=len(piv);m[k],m[r]=m[r],m[k];v=m[k][c];m[k]=[t/v for t in m[k]]
  for r in range(nr):
   if r!=k and m[r][c]:
    v=m[r][c];m[r]=[u-v*w for u,w in zip(m[r],m[k])]
  piv.append(c)
 basis=[]
 for c in range(nc):
  if c not in piv:
   v=[F(0)]*nc;v[c]=F(1)
   for i,j in enumerate(piv):v[j]=-m[i][c]
   basis.append(v)
 return basis
x=[-1,1,0,0,-1,1,0,1,1,-2,0,1,1,-1,1]
g=[int(i in [0,1,3,6,7,8,12,13]) for i in range(15)]
B,A=matrix(g,15);basis=ker(A);odd=range(0,15,2);even=range(1,15,2)
C=[[A[i][j] for j in even] for i in odd];O=[[A[i][j] for j in odd] for i in odd]
res={'B':B,'A':A,'Ax':[sum(a*b for a,b in zip(r,x)) for r in A],'odd_copy':all(A[2*i][2*j]==A[i][j] for i in range(8) for j in range(8)),'even_null':all(A[i][j]==0 for i in even for j in even),'nullity':len(basis),'basis':[[str(t) for t in v] for v in basis],'basis_odd_parts':[[str(t) for t in v[::2]] for v in basis],'rank_D':8-len(ker(O+list(map(list,zip(*C))))),'nullity_B':len(ker(C)),'BXe':[sum(A[i][j]*x[j] for j in even) for i in odd]}
(D/'math-witness.json').write_text(json.dumps(res,indent=2));print(json.dumps(res))
coverage=[]
# All prefixes satisfying the infinite io recurrence; no modular filtering.
for n in range(2,16):
 free=list(range(2,n-1,2));total=0;bad=[]
 for mask in range(1<<len(free)):
  g=[1]+[0]*(n-1)
  for i in range(1,n):g[i]=g[i//2] if i%2 else ((mask>>free.index(i))&1 if i in free else 0)
  _,a=matrix(g,n);ks=ker(a);total+=1
  if any(any(v[::2]) for v in ks):bad.append({'mask':mask,'g':g,'basis':[[str(t) for t in v] for v in ks]})
 coverage.append({'n':n,'prefixes':total,'counterexamples':len(bad),'first':bad[:1]});print(coverage[-1],flush=True)
(D/'search.json').write_text(json.dumps(coverage,indent=2))
