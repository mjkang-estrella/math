from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial
import json
L=Path(__file__).resolve().parent
def q(m):return [F((-1)**j*comb(m,j)*factorial(2*m-j),factorial(2*m)) for j in range(m+1)]
def inverse(q,N):
 c=[F(1)]
 for n in range(1,N+1):c.append(-sum(q[j]*c[n-j] for j in range(1,min(n,len(q)-1)+1)))
 return c
rows=[]
for m in range(1,20,2):
 a=q(m);prod=[sum((a[i]*a[j]*(-1)**j for i in range(m+1) for j in range(m+1) if i+j==k),F(0)) for k in range(2*m+1)]
 assert all(prod[k]==0 for k in range(1,len(prod),2))
 d=prod[::2]
 for j in range(m+1):
  formula=F((-1)**j*comb(m,j)*factorial(2*m-j)*factorial(m)*factorial(2*m-2*j),factorial(2*m)**2*factorial(m-j))
  assert d[j]==formula
 c=inverse(d,160)
 rows.append({'m':m,'w_degree_bound':160,'nonpositive':{i:str(v) for i,v in enumerate(c) if v<=0},'first_coefficients':[str(v) for v in c[:8]]})
(L/'product-route.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
