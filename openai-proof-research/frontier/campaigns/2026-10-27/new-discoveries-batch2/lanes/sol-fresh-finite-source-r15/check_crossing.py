import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(20,20))
from math import comb
from fractions import Fraction as F
import pathlib,json
out={'cases':0,'first_H_decrease':None}
for a in [F(1,10),F(1,2),F(1),F(2),F(10)]:
 for l in [1,2,3,5,8,12,20,40]:
  for m in range(2,41):
   D=[sum((comb(r,i)*a**i)**l for i in range(r+1)) for r in range(m+1)]
   N=0;H=[]
   for r in range(m):
    N+=(comb(m,r)*a**r)**l
    H.append(N*(D[r+1]-D[r])/(D[r]*(comb(m,r+1)*a**(r+1))**l))
   out['cases']+=1
   for r in range(m-1):
    if H[r]>H[r+1]:out['first_H_decrease']={'a':str(a),'l':l,'m':m,'r':r,'H_r':str(H[r]),'H_next':str(H[r+1])};break
   if out['first_H_decrease']:break
  if out['first_H_decrease']:break
 if out['first_H_decrease']:break
pathlib.Path(__file__).with_name('crossing-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
