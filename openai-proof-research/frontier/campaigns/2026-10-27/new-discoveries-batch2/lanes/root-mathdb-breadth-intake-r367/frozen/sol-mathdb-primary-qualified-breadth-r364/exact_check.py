from fractions import Fraction as F
from math import gcd
from pathlib import Path
import json
count=0
for n in range(1,25):
 b=[F(0)]+[F(k,n)-F(1,2) for k in range(1,n)]
 c=[F(k,n)**2-F(k,n)+F(1,6) for k in range(n)]
 for t in range(n):assert sum(b[k]*b[(k-t)%n] for k in range(n))==F(n,2)*c[t]+F(1,6*n)-(F(1,4) if t==0 else 0)
 for z in range(1,n+1):
  if gcd(z,n)!=1:continue
  iz=pow(z,-1,n)
  s=lambda a:sum(b[k]*b[l]*c[(a*(k-l))%n] for k in range(1,n) for l in range(1,n))
  assert s(z)==s(iz)==F(n,2)*sum(c[t]*c[z*t%n] for t in range(n))+F(1,36*n*n)-F(1,24)
  count+=1
(Path(__file__).parent/'exact-check.json').write_text(json.dumps({'status':'PASS','N_range':[1,24],'unit_cases':count,'arithmetic':'fractions.Fraction exact','proof':False},indent=2)+'\n')
print('PASS',count)
