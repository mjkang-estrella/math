import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(20,20))
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
P=Path(__file__).parent
nchecks=0
for m in range(2,25):
 for l in [1,2,3,5,8]:
  for a in [F(1,10),F(1),F(3)]:
   D=[sum((comb(r,i)*a**i)**l for i in range(r+1)) for r in range(m+1)]
   u=[(comb(m,r)*a**r)**l for r in range(m+1)]
   N=[];z=0
   for x in u:z+=x;N.append(z)
   S=[N[r]/D[r] for r in range(m+1)]
   Q=[N[r]/u[r+1] for r in range(m)]
   T=[D[r]/(D[r+1]-D[r]) for r in range(m)]
   assert all(D[r+1]>D[r] for r in range(m))
   assert all(Q[r+1]>Q[r] for r in range(m-1))
   for r in range(m):
    assert S[r+1]-S[r]==u[r+1]/D[r+1]*(1-Q[r]/T[r]); nchecks+=1
D=[sum(comb(r,i)**5 for i in range(r+1)) for r in range(4)]
assert D==[1,2,34,488]
assert D[2]**2>D[1]*D[3]
assert F(D[1],D[2]-D[1])<F(D[2],D[3]-D[2])
m,l=5,6;S=[F(sum(comb(m,i)**l for i in range(r+1)),sum(comb(r,i)**l for i in range(r+1))) for r in range(m+1)]
bad=[r for r in range(1,m) if S[r]**2<S[r-1]*S[r+1]]
assert bad
out={'adjacent_sign_identity_checks':nchecks,'denominator_obstruction':D,'T1':str(F(1,16)),'T2':str(F(17,227)),'logconcavity_witness':{'m':5,'l':6,'a':1,'S':list(map(str,S)),'failed_indices':bad},'status':'PASS','source_refutation':False}
(P/'bridge-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
