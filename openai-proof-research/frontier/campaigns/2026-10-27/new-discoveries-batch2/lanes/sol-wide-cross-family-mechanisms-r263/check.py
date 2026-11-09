from research import *
from fractions import Fraction as F
import math
out={'sparse':[],'real_rooted':[],'failures':[]}
for t in range(1,8):
 p=3**t;m=p*t;assert 3**m==p**p<=(m+1)**p
 # f=z+3^m*z^(m+1), only nonzero initial coefficient a_1=1.
 out['sparse'].append(dict(t=t,p=p,m=m,degree=m+1,all_tail_nonzero_indices=[m+1],inequality=True,simple_zeros_in_half_disc=m+1))
for p in [5,10,25]:
 t=0
 while 5**(t+1)<=p:t+=1
 m=p*t;a=[F(1)]
 for j in range(1,m+1):
  c=3+F(j,m+1);a.append(F(0))
  for k in range(len(a)-1,0,-1):a[k]-=c*a[k-1]
 M=max(abs(v) for v in a[:p+1]);assert sum(abs(v) for v in a)<5**m<=p**p
 assert all(abs(a[k])<=k**p*M for k in range(p+1,len(a)))
 out['real_rooted'].append(dict(p=p,t=t,m=m,coefficients_checked=len(a),distinct_real_roots=True,l1_bound=True))
out['failures'].append(dict(route='Uniform coefficient summation / source Theorem 2.3',status='Does not prove linear valency: maximizing k^p*r^k has k about p/abs(log r), log maximum of order p log p. The source already records this loss.'))
(L/'exact-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
