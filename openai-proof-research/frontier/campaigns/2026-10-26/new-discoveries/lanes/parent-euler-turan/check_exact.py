from fractions import Fraction as F
from math import comb,factorial
from pathlib import Path
import json,random
E=[1,1]
for n in range(1,95):E.append(sum(comb(n,k)*E[k]*E[n-k] for k in range(n+1))//2)
a=[F(E[n],factorial(n)) for n in range(len(E))];checks=0
for n in range(25):
 for j in range(1,25):
  for k in range(1,25):
   assert (-1)**(n+1)*(a[n]*a[n+j+k]-a[n+j]*a[n+k])>0,(n,j,k)
   checks+=1
random.seed(338918);abstract=0
for _ in range(100):
 c=[F(random.randint(1,999),1000),F(random.randint(1,999),1000)]
 for n in range(80):c.append(c[n]*F(random.randint(1,1000),3000))
 b=[1+(-1)**(n+1)*c[n] for n in range(len(c))]
 for n in range(8):
  for j in range(1,8):
   for k in range(1,8):
    assert (-1)**(n+1)*(b[n]*b[n+j+k]-b[n+j]*b[n+k])>0
    abstract+=1
out={'scope':'Finite exact checks only, not proof or discovery credit','source_Euler_checks':checks,'independent_abstract_error_sequence_checks':abstract,'all_pass':True}
Path('exact-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
