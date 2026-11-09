from fractions import Fraction as F
from pathlib import Path
import json,sys
D=Path(__file__).resolve().parents[1];N=int(sys.argv[1]);p={():F(1)};out=[]
def parts(n,m):
 if n==0:yield ();return
 for x in range(min(n,m),1-1,-1):
  for tail in parts(n-x,x):yield (x,)+tail
for n in range(1,N+1):
 maxp=F(0);arg=None;count=0
 for b in parts(n,n):
  ps=F(0)
  for i,row in enumerate(b):
   for j in range(row):
    c=b[:i]+tuple(min(x,j) for x in b[i:] if min(x,j)>0)
    ps+=1-p[c]
  p[b]=ps/n
  if len(b)>1 and b[0]>1:
   count+=1
   if p[b]>maxp:maxp=p[b];arg=b
   if p[b]>=F(1,2):print('COUNTEREXAMPLE',b,str(p[b]),flush=True)
 r=dict(n=n,count=count,maximum=str(maxp),arg=arg,states=len(p));print(r,flush=True);out.append(r)
 (D/'outputs/chomp.json').write_text(json.dumps(out,indent=2)+'\n')
