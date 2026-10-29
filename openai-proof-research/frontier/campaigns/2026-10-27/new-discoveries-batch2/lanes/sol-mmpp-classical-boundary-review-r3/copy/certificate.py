from math import factorial
import json,pathlib
K=80;a=[9,8,7,6,5,4,3,4,5,6,7,8];x=[1]*12
N=0;D=72*25**K*factorial(K)
for k in range(K+1):
 N+=4**k*25**(K-k)*(factorial(K)//factorial(k))*sum((6-a[i])*x[i] for i in range(12))
 x=[60*x[(i+1)%12]+(9-a[i])*x[i] for i in range(12)]
assert N < -2*D
out={'K':K,'rate_numerators_over_60':a,'denominator':str(D),'numerator':str(N),'N_plus_2D':str(N+2*D),'certificate':'N<-2D; exact integer recurrence in certificate.py'}
(pathlib.Path(__file__).parent/'certificate.json').write_text(json.dumps(out,indent=2));print('Integer certificate PASS; numerator digits',len(str(abs(N))))
