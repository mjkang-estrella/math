"""Exact bounded factor diagnostics; only individual trace summands are probed."""
from collections import defaultdict,Counter
from itertools import permutations
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def divide(a,b):
 a=a[:];c=[0]*max(1,len(a)-len(b)+1)
 while len(a)>=len(b):
  if a[-1]%b[-1]:return None
  z=a[-1]//b[-1];p=len(a)-len(b);c[p]=z
  for j,y in enumerate(b):a[p+j]-=z*y
  while a and a[-1]==0:a.pop()
 return c if not a else None
def weights(s,N):
 red=lambda i:i<=0 or i in s
 W=[i for i in range(1,N+2) if not red(i) and red(i-1)]
 R=[i for i in range(1,N+2) if red(i) and not red(i-1)]
 for y in W:
  if y>N:continue
  fac=Counter({y:1});q=0;sign=1
  for n,exp in [(y-b,1) for b in R]+[(y-a,-1) for a in W if a!=y]:
   if n<0:q+=n*exp;sign=-sign;n=-n
   fac[n]+=exp
  assert sign==1
  yield s[1:]+(y,),fac,q,y

def run():
 total=0;examples=[]
 for N in (3,4,5):
  for k in range(1,N):
   for start in permutations(range(1,N+1),k):
    def walk(s,fac,qp,ys,depth):
     nonlocal total
     if depth>=2 and s==start:
      total+=1
      num=den=[1]
      for n,ex in fac.items():
       for _ in range(abs(ex)):
        if ex>0:num=mul(num,[1]*n)
        else:den=mul(den,[1]*n)
      poly=divide(num,den)
      if (poly is None or min(poly)<0 or qp<0) and len(examples)<12:
       examples.append(dict(N=N,k=k,start=start,append=ys,q_power=qp,qintegers=dict(fac),polynomial=poly))
     if depth==6:return
     for t,f,p,y in weights(s,N):
      nxt=fac.copy();nxt.update(f)
      walk(t,nxt,qp+p,ys+[y],depth+1)
    walk(start,Counter(),0,[],0)
 (ROOT/'notes/closed-weight-diagnostics.json').write_text(json.dumps(dict(closed_walks=total,examples=examples),indent=2)+'\n')
 print(json.dumps(dict(closed_walks=total,examples=examples[:4]),indent=2))
if __name__=='__main__':run()
