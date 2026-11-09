from pathlib import Path
from fractions import Fraction as F
from math import isqrt,comb,prod,exp
from itertools import product
import json
D=Path(__file__).resolve().parent
out={'executed':True,'spectral':[],'wecken':[]}
for k in range(1,8):
 for A in [list(range(1,k+1)),[2**i for i in range(k)],[3**i for i in range(k)]]:
  vals=set()
  for a,b,c,d in product(A,repeat=4):
   t=a+d;disc=(a-d)**2+4*b*c;s=isqrt(disc)
   vals.add(('rational',F(t+s,2)) if s*s==disc else ('irrational',t,disc))
  out['spectral'].append({'A':A,'exact_count':len(vals),'conjectured_minimum':(2*k**3-k*k+k)//2})
for n in [3,5,10,20,50]:
 den=n*(2*n-1)**2;total=0.;cs=[]
 for c in range(n+1):
  sc=0.
  for b in range(n-c+1):
   K=prod((4*(n-1)**4-(8*j-6)*(n-1)**2+4*j*j-6*j+2)/(n*(n-1)*(2*n-1)**2) for j in range(c+b+1,n+1))
   B=prod((2*(n-1)**2-(2*c+b+j-1))/den for j in range(1,b+1))
   sc+=comb(n,c)*comb(n-c,b)*2**b*((n-1)/den)**c*K*B
  total+=sc;cs.append(sc)
 out['wecken'].append({'n':n,'float_dstar':total,'c0_contribution':cs[0],'positive_c_total':sum(cs[1:]),'target':exp(-2)})
# Verify the polynomial expansion identity used by the route at finite rational samples.
for n in range(3,41):
 for k in range(1,n+1):
  den=n*(n-1)*(2*n-1)**2;num=4*(n-1)**4-(8*k-6)*(n-1)**2+4*k*k-6*k+2
  assert 0<num<=den
  assert den-num==8*n**3+(8*k-25)*n*n+(27-16*k)*n-4*k*k+14*k-12
out['K_factor_check']={'n_range':[3,40],'executed_exact':True,'result':'all factors positive and <=1; expansion identity verified on samples, not universal proof'}
(D/'bounded-calculation.json').write_text(json.dumps(out,indent=2,default=str)+'\n')
print(json.dumps(out,indent=2,default=str))
