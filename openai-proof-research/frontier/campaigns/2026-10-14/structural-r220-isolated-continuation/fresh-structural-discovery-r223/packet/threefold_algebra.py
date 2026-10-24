"""Exact tiny determinantal-divisor calculation, no package installation."""
from itertools import combinations
from math import gcd
from pathlib import Path
import json

def det(a):
 n=len(a)
 if not n:return 1
 b=[x[:] for x in a]; sign=1; prev=1
 for k in range(n-1):
  pivot=next((i for i in range(k,n) if b[i][k]),None)
  if pivot is None:return 0
  if pivot!=k:b[k],b[pivot]=b[pivot],b[k];sign=-sign
  q=b[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    z=b[i][j]*q-b[i][k]*b[k][j]
    assert z%prev==0
    b[i][j]=z//prev
  for i in range(k+1,n):b[i][k]=0
  prev=q
 return sign*b[-1][-1]

def minor(a,I,J):return det([[a[i][j] for j in J] for i in I])
def smith(a):
 n=len(a);divs=[1]
 for k in range(1,n+1):
  ix=list(combinations(range(n),k));d=0
  for I in ix:
   for J in ix:d=gcd(d,minor(a,I,J))
  if not d:break
  assert d%divs[-1]==0
  divs.append(d)
 return [divs[i]//divs[i-1] for i in range(1,len(divs))]+[0]*(n-len(divs)+1)

A2=[[-int(i==j) for j in range(4)] for i in range(4)]
A3=[[0,-1,0,0],[1,-1,0,0],[0,0,0,-1],[0,0,1,-1]]
out=[]
for p,A in [(2,A2),(3,A3)]:
 for k in range(5):
  ix=list(combinations(range(4),k))
  W=[[minor(A,I,J)-int(i==j) for j,J in enumerate(ix)] for i,I in enumerate(ix)]
  d=smith(W)
  out.append(dict(p=p,k=k,wedge_minus_identity=W,smith=d,free=d.count(0),torsion=[v for v in d if v>1]))
r=Path(__file__).parent
(r/'private/threefold-algebra.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k!='wedge_minus_identity'} for x in out],indent=2))
