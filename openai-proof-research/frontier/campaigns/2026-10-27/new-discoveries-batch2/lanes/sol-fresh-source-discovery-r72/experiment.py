import numpy as np,random,json,math
from fractions import Fraction as F
random.seed(720)
def dist(a):
 d=np.array([1.])
 for b in a:
  v=np.zeros(len(d)+2*b);v[:len(d)]+=d/2;v[2*b:]+=d/2;d=v
 return d
ps=[2.001,2.01,2.05,2.2,2.5,2.9]
worst=[(float('inf'),None) for p in ps];cnt=0
for n in range(1,13):
 for it in range(400):
  a=[random.randint(1,24) for _ in range(n)]
  if it<20:a=[1]*n
  d=dist(a);e=np.convolve(d,d);x=np.abs(np.arange(len(d))-sum(a));y=np.abs(np.arange(len(e))-2*sum(a))/math.sqrt(2)
  v=sum(b*b for b in a)
  for k,p in enumerate(ps):
   old=float(np.dot(d,x**p));new=float(np.dot(e,y**p));gap=(new-old)/v**(p/2)
   if gap<worst[k][0]:worst[k]=(gap,a)
  cnt+=1
out={'status':'floating diagnostics only','samples':cnt,'powers':ps,'worst':worst}
json.dump(out,open('experiment.json','w'),indent=2);print(json.dumps(out))
