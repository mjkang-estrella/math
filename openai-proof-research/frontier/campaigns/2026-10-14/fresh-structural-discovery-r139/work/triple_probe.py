from itertools import combinations
from collections import defaultdict
from fractions import Fraction as F
import json

def connected(n,edges):
 seen={0}
 while True:
  z=seen|{v for a,b in edges for u,v in [(a,b),(b,a)] if u in seen}
  if z==seen:return len(z)==n
  seen=z

def neg_witness(A):
 n=len(A);A=[list(map(F,r)) for r in A];V=[[F(i==j) for i in range(n)] for j in range(n)]
 for i in range(n):
  d=A[i][i]
  if d<0:return V[i]
  if not d:
   for j in range(i+1,n):
    if A[i][j]:
     t=-A[i][j]/(abs(A[j][j])+1);return [x+t*y for x,y in zip(V[i],V[j])]
   continue
  r=[A[i][j]/d for j in range(n)]
  for j in range(i+1,n):
   V[j]=[x-r[j]*y for x,y in zip(V[j],V[i])]
   for k in range(j,n):A[j][k]=A[k][j]=A[j][k]-r[j]*A[i][k]
 return None

for n in range(4,7):
 ed=list(combinations(range(n),2));groups=defaultdict(list)
 for bits in range(1<<len(ed)):
  E=frozenset(e for j,e in enumerate(ed) if bits>>j&1)
  if not connected(n,E):continue
  deg=tuple(sum(v in e for e in E) for v in range(n))
  key=(deg,tuple(e for e in E if min(e)>=3),tuple(sum(tuple(sorted((i,w))) in E for i in range(3)) for w in range(3,n)))
  groups[key].append(E)
 checked=0
 for key,states in groups.items():
  k=len(states)
  if k<2:continue
  H=[[F(3*(i==j)) for j in range(k)] for i in range(k)]
  for a in combinations(range(3),2):
   fs=defaultdict(list)
   for i,E in enumerate(states):
    fs[(tuple(sorted(e for e in E if not (set(e)&set(a)))),a in E,tuple(sum(tuple(sorted((v,w))) in E for v in a) for w in range(n) if w not in a))].append(i)
   for ids in fs.values():
    for i in ids:
     for j in ids:H[i][j]-=F(1,len(ids))
  A=[[H[i][j]-F(i==j)+F(1,k) for j in range(k)] for i in range(k)]
  w=neg_witness(A);checked+=1
  if w is not None:
   mean=sum(w)/k;w=[v-mean for v in w]
   q=sum(w[i]*A[i][j]*w[j] for i in range(k) for j in range(k));assert q<0
   print(json.dumps(dict(n=n,checked=checked,states=[sorted(E) for E in states],witness=list(map(str,w)),quadratic=str(q),degree=key[0]),indent=2));raise SystemExit
 print(json.dumps(dict(n=n,nonconstant_cells=checked,status='no negative H_T-I on centered space found')),flush=True)
