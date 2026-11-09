from fractions import Fraction as F
import json,pathlib
L=pathlib.Path(__file__).resolve().parent
r=[F(1),F(4,5),F(169,250),F(319,500)]
alpha=[];c=[];v=F(1)
for n in range(1,4):
 a=(r[n]-sum((c[j-1]*r[n-j] for j in range(1,n)),F(0)))/v
 c=[c[j-1]-a*c[n-j-1] for j in range(1,n)]+[a]
 alpha.append(a);v*=1-a*a
assert alpha==[F(4,5),F(1,10),F(1,5)]
assert c==[F(7,10),F(-11,250),F(1,5)]
assert all(r[j]>r[j+1]>0 for j in range(3))
assert r[1]**2<=r[0]*r[2] and r[2]**2<=r[1]*r[3]
def det(a):
 a=[x[:] for x in a];d=F(1)
 for j in range(len(a)):
  q=a[j][j];assert q>0;d*=q
  for k in range(j+1,len(a)):
   z=a[k][j]/q
   for m in range(j,len(a)):a[k][m]-=z*a[j][m]
 return d
dets=[det([[r[abs(j-k)] for j in range(n)] for k in range(n)]) for n in range(1,5)]
u=F(1,10);w=F(3);sign=4*u*u*(4*u*u+2*u*w-1)
assert sign==F(-9,625)
o={'ar_covariance':list(map(str,r)),'positive_partial_correlations':list(map(str,alpha)),'predictor_coefficients':list(map(str,c)),'leading_toeplitz_determinants':list(map(str,dets)),'hcm_second_derivative_exponential_factor':str(sign),'status':'PASS exact rational checks; neither numerical evidence for fGn nor novelty evidence'}
(L/'boundedchecks.json').write_text(json.dumps(o,indent=2));print(json.dumps(o,indent=2))
