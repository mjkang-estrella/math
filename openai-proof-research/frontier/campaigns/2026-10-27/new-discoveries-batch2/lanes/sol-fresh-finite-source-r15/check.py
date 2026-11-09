import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(45,45))
from math import comb
from fractions import Fraction
import json,pathlib,time
P=pathlib.Path(__file__).parent
cases=0; violations=[]; lc=[]
for a in [Fraction(1,10),Fraction(1,3),Fraction(1,2),Fraction(1),Fraction(2),Fraction(3),Fraction(10)]:
 for l in [1,2,3,4,5,8,12,20,40]:
  D=[sum((comb(r,i)*a.numerator**i*a.denominator**(r-i))**l for i in range(r+1)) for r in range(61)]
  for m in range(2,61):
   N=0; S=[]
   for r in range(m+1):
    N+=(comb(m,r)*a.numerator**r*a.denominator**(m-r))**l
    S.append(Fraction(N*a.denominator**(r*l),D[r]*a.denominator**(m*l)))
   down=False
   for r in range(m):
    if S[r]>S[r+1]:down=True
    if down and S[r]<S[r+1]:violations.append({'m':m,'l':l,'a':str(a),'rise':r});break
   if any(S[r]**2<S[r-1]*S[r+1] for r in range(1,m)) and len(lc)<15:lc.append({'m':m,'l':l,'a':str(a)})
   cases+=1
   if violations:break
  if violations:break
 if violations:break
out={'cases':cases,'unimodality_violations':violations,'first_logconcavity_failures':lc,'proof':False};(P/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
