import json,sys
from pathlib import Path
from sympy.combinatorics import Permutation,PermutationGroup
from math import factorial
L=Path(__file__).resolve().parent
def rev(n,q):return Permutation(list(range(q-1,-1,-1))+list(range(q,n)))
rows=[]
for k in range(2,13):
 target=k+1 if k%2==0 else (k+1)//2
 best=[]; bestn=None;tests=[]
 for n in range(k+2,4*k+13):
  ms=[]
  for m in range(max(k+1,n-k-1),n):
   G=PermutationGroup([rev(n,q) for q in [n,m,k]])
   order=int(G.order())
   if order==factorial(n):ms.append(m)
  tests.append([n,ms])
  if len(ms)>len(best):best,bestn=ms,n
  if len(best)>=target:break
 rows.append(dict(k=k,target=target,bestn=bestn,best=best,tests=tests));print(k,target,bestn,best,flush=True)
(L/'checks.json').write_text(json.dumps(rows,indent=2)+'\n')
