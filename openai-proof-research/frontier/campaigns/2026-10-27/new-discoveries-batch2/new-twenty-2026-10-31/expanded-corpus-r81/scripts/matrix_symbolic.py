from pathlib import Path
from math import comb,factorial
from collections import defaultdict
from itertools import combinations
from fractions import Fraction
import json
D=Path(__file__).resolve().parents[1];T=json.loads((D/'outputs/T.json').read_text());T=[r[:10] for r in T[:10]]
def det(A):
 a=[[Fraction(x) for x in r] for r in A];sign=1
 for k in range(len(a)):
  j=next((j for j in range(k,len(a)) if a[j][k]),None)
  if j is None:return 0
  if j!=k:a[k],a[j]=a[j],a[k];sign=-sign
  for j in range(k+1,len(a)):
   r=a[j][k]/a[k][k]
   for l in range(k+1,len(a)):a[j][l]-=r*a[k][l]
 ans=Fraction(sign)
 for k in range(len(a)):ans*=a[k][k]
 assert ans.denominator==1;return int(ans)
e={0:{(0,)*10:1}}
for k in range(1,11):
 e[k]={}
 for vs in combinations(range(10),k):
  d=det([[T[i][j] for j in vs] for i in vs])
  if d:e[k][tuple(int(i in vs) for i in range(10))]=d
assert all(not e[k] for k in range(7,11))
def exps(n,d):
 if n==1:yield (d,);return
 for k in range(d+1):
  for tail in exps(n-1,d-k):yield (k,)+tail
rows=[]
for j in range(7):
 p=defaultdict(int)
 for k in range(7-j):
  d=6-k-j
  for b in exps(10,d):
   multin=factorial(d)
   denom=1
   for bi in b:denom*=factorial(bi)
   multin//=denom
   for a,c in e[k].items():p[tuple(x+y for x,y in zip(a,b))]+=c*comb(6-k,j)*3**(k+j)*multin
 neg=[{'exponents':list(a),'coefficient':c} for a,c in p.items() if c<0];rows.append({'t_power':j,'nonzero_monomials':sum(c!=0 for c in p.values()),'negative_monomials':len(neg),'examples':neg[:5]})
 print(rows[-1],flush=True)
(D/'outputs/matrix-symbolic.json').write_text(json.dumps({'interpretation':'Coefficients of 3^6 p6(n/3+t), n=sum x, p6 is rank-six nonzero characteristic factor det(zI+T_x). Exact principal-minor expansion.','principal_minor_nonzero_counts':{k:len(v) for k,v in e.items()},'shifted_coefficients':rows},indent=2)+'\n')
