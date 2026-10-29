import json,time
from sympy import Matrix,primerange
from math import factorial
from fractions import Fraction
def val(n,p):
 c=0
 while n%p==0:c+=1;n//=p
 return c
for n in (60,100):
 ps=list(primerange(2,n+1));m=n-1
 A=[[sum(val(k,p) for k in range(2,t+1))-t*val(t,p) for p in ps] for t in range(2,n+1)]
 M=Matrix([[int(i==j) for j in range(m)]+[10000000*a for a in A[i]] for i in range(m)])
 start=time.monotonic();L=M.lll(delta=0.75)
 best=None
 for row in L.tolist():
  if any(row[m:]):continue
  norm=max(map(abs,row[:m]));best=norm if best is None else min(norm,best)
  if norm==1:
   left=[i+2 for i in range(m) if row[i]==1];right=[i+2 for i in range(m) if row[i]==-1]
   def prod(ts):
    x=Fraction(1)
    for t in ts:x*=Fraction(factorial(t),t**t)
    return x
   assert prod(left)==prod(right)
   print(json.dumps({'n':n,'left':left,'right':right,'exact_equal':True}),flush=True)
 print(json.dumps({'n':n,'best_max_coefficient':int(best) if best else None,'seconds':time.monotonic()-start}),flush=True)
