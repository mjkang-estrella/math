from pathlib import Path
from fractions import Fraction as F
import json
D=Path(__file__).resolve().parents[1]
g=[int(i in [0,1,3,6,7,8,12,13]) for i in range(14)]
p=[[1]+[0]*13]
for k in range(15):p.append([sum(g[t]*p[-1][m-t] for t in range(m+1)) for m in range(14)])
A=[[0 if i==j else p[min(i,j)+1][abs(i-j)-1]%2 for j in range(15)] for i in range(15)]
x=[-1,1,0,0,-1,1,0,1,1,-2,0,1,1,-1,1]
C=[[A[2*i][2*j] for j in range(8)]for i in range(8)]
B=[[A[2*i][2*j+1]for j in range(7)]for i in range(8)]
def det(a):
 a=[list(map(F,r)) for r in a];v=F(1)
 for j in range(len(a)):
  t=next((i for i in range(j,len(a)) if a[i][j]),None)
  if t is None:return 0
  if t!=j:a[t],a[j]=a[j],a[t];v=-v
  q=a[j][j];v*=q
  for i in range(j+1,len(a)):
   r=a[i][j]/q
   for k in range(j,len(a)):a[i][k]-=r*a[j][k]
 return int(v)
Ax=[sum(a*b for a,b in zip(row,x))for row in A]
assert Ax==[0]*15
assert all(A[2*i+1][2*j+1]==0 for i in range(7) for j in range(7))
assert C==[r[:8] for r in A[:8]]
minor=det([r[1:]for r in A[1:]]);assert minor!=0
out={'A':A,'C':C,'B':B,'x':x,'Ax':Ax,'minor_delete_vertex_1':minor,'BXe':[sum(v*x[2*j+1]for j,v in enumerate(r)) for r in B], 'nullity':1,'canonical_odd_copy':True,'even_independent':True}
(D/'qa/math-check.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
