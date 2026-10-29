from check import neighbors,closure
import json
from pathlib import Path

def scan(m,n):
 N=m*n;allmask=(1<<N)-1;nb=neighbors(m,n)
 ok=[closure(allmask^v,nb)==allmask for v in range(1<<N)]
 tests=0
 for union in range(1<<N):
  inter=union
  while True:
   D=union^inter;d=D.bit_count();c=[0]*(d+1);x=D
   while True:
    if ok[inter|x] and ok[inter|(D^x)]:c[x.bit_count()]+=1
    if x==0:break
    x=(x-1)&D
   tests+=1
   for r in range(d//2):
    if c[r]>c[r+1]:return {'m':m,'n':n,'tests':tests,'inter':inter,'union':union,'slice':c,'failure':r}
   if inter==0:break
   inter=(inter-1)&union
 return {'m':m,'n':n,'tests':tests,'no_slice_failure':True}
res=[scan(m,n) for m,n in [(2,4),(3,3),(3,4)]]
Path('slices.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res))
