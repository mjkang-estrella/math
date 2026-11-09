from math import comb
from itertools import combinations_with_replacement
import random,json,time

def polyprod(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c

def dec(c,i):
 rem=c; cap=None; g=h=0
 for r in range(i,0,-1):
  if not rem: break
  lo=r-1;hi=r+1 if cap is None else cap
  if cap is None:
   while comb(hi,r)<=rem:hi*=2
  while hi-lo>1:
   mid=(hi+lo)//2
   if comb(mid,r)<=rem:lo=mid
   else:hi=mid
  a=lo
  rem-=comb(a,r)
  g+=comb(a-1,r) if a-1>=r else 0
  h+=comb(a-1,r-1)
  cap=a
 assert rem==0
 return g,h

def check(f):
 d=len(f)-1;g=[1];h=[]
 for i,c in enumerate(f[1:],1):
  x,y=dec(c,i);g.append(x);h.append(y)
 for i in range(1,d):
  if h[i]>g[i]:return i,g,h

random.seed(97531)
best=[];start=time.time()
for it in range(250000):
 f=[1];factors=[]
 d=random.randint(3,24)
 while len(f)-1<d:
  if random.randrange(2) and len(f)<d:
   a=random.randint(2,100);b=random.randint(1,a*a//4);fac=[1,a,b]
  else: fac=[1,random.randint(1,100)]
  f=polyprod(f,fac);factors.append(fac)
 r=check(f)
 if r:
  out={'iteration':it,'f':f,'factors':factors,'violation':r};json.dump(out,open('recursive-violation.json','w'),indent=2);print(out);break
else:print('No violations',it+1,'seconds',time.time()-start)
