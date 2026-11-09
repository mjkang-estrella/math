import os,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
import sympy as S
x,a,s,p=S.symbols('x a s p');b=1-a;z=x-2*a-p;q=b*b/z

def mat(ds):
 m=S.diag(*ds)
 for i,j in [(0,1),(1,2),(2,3),(3,0),(1,3)]:m[i,j]=m[j,i]=-b
 return m
# all arms nonempty; s3=s, s5=s+1. p=h_(l-1), q=h_l.
for parity in ['even','odd']:
 ds3=[x-2*a,x-a*(s+4)-s*b*b/(x-a)-q,x-2*a,x-4*a-(p if parity=='even' else q)]
 ds5=[x-3*a-(p if parity=='even' else q),x-a*(s+4)-(s+1)*b*b/(x-a),x-3*a-p,x-3*a]
 d3=mat(ds3).det(method='domain-ge');d5=mat(ds5).det(method='domain-ge');diff=S.factor(z*d3-(x-a)*d5)
 print(parity,'normalized characteristic difference:',diff,flush=True)
 print('numerator expanded in s:',S.Poly(S.fraction(diff)[0],s),flush=True)
