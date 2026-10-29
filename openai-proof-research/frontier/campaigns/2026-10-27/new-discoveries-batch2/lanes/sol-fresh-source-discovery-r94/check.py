from pathlib import Path
from fractions import Fraction as F
import json,math
import numpy as np
from scipy.special import roots_hermitenorm,eval_hermitenorm
p=Path(__file__).parent
# Exact generating-function coefficient identity exp(z*x-z²/2) for convolution.
identities=0
for n in range(17):
 for k in range(n+1):
  # product identity H_k(X)H_(n-k)(Y) under conditional standard Gaussian
  # checked combinatorial coefficient in independent two-variable generating series
  assert F(math.comb(n,k),math.factorial(n))==F(1,math.factorial(k)*math.factorial(n-k));identities+=1
# Moment ratio of f_a to Gaussian: E X^(2j)/(2j-1)!!=1+4j(j-1)a.
a=F(1,222); vm=[F(1)+4*j*(j-1)*a for j in range(5)]
central4=vm[4]-4*vm[3]+6*vm[2]-4*vm[1]+vm[0]
assert central4==0 and vm[2]-vm[1]**2>0 # forbids Gaussian variance mixture representation.
for N in [96,192]:
 x,w=roots_hermitenorm(N);w=w/math.sqrt(2*math.pi);h4=eval_hermitenorm(4,x);h8=eval_hermitenorm(8,x)
 worst=(-float('inf'),None);total=0;mins=1e99
 for a0 in [1/222,1/444,1/888,1/1776]:
  for q in [1/64,1/16,1/8,1/4,3/8,1/2,4/7,0.58,0.75,1.0]:
   b=a0*q*q
   for t in np.linspace(0,1,65):
    A=t*t+(1-t)**2;Ap=4*t-2;App=4
    B=t*t*(1-t)**2;Bp=2*t*(1-t)*(1-2*t);Bpp=2-12*t+12*t*t
    R=1+b*A*h4+b*b*B*h8;Rp=b*Ap*h4+b*b*Bp*h8;Rpp=b*App*h4+b*b*Bpp*h8
    assert np.min(R)>0
    value=-np.dot(w,Rpp*np.log(R)+Rp*Rp/R)/(b*b)
    mins=min(mins,float(np.min(R)))
    if value>worst[0]:worst=(float(value),[a0,q,float(t)])
    total+=1
  # global strong log-concavity from r-24ay=a(y-15)^2+1-222a>=0.
 assert worst[0]<0
 result={'nodes':N,'cases':total,'largest_scaled_curvature':worst,'min_ratio_at_nodes':mins}
 (p/f'quadrature-{N}.json').write_text(json.dumps(result,indent=2));print(result)
(p/'exact-checks.json').write_text(json.dumps({'coefficient_identities':identities,'mixing_central_fourth':str(central4),'mixing_variance':str(vm[2]-1),'strong_logconcavity_range':'0<a<=1/222','status':'exact identities plus unvalidated numerical quadrature; no proof of source'},indent=2))
