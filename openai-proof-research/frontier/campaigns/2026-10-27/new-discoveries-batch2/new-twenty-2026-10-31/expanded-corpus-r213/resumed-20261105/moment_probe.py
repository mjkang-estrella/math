from functools import lru_cache
import json
# q=1, arbitrary integer corolla values; compare derived chain with NC moments.
weights=[1,2,3,5,7,11,13,17,19,23,29]
def splits(t):
 for i,v in enumerate(t):
  for j,w in enumerate(v):
   if w:continue
   yield tuple(sorted(t[:i]+t[i+1:]+(v[:j]+v[j+1:],w))),tuple(sorted(t[:i]+t[i+1:]+((),))),v
  for a,b,c in splits(v):yield tuple(sorted(t[:i]+t[i+1:]+(a,))),tuple(sorted(t[:i]+t[i+1:]+(b,))),c
@lru_cache(None)
def f(t):
 if all(not x for x in t):return weights[len(t)]
 a,b,c=next(splits(t));return f(a)+f(b)*f(c)
m=[1]
for n in range(1,10):
 # coefficient recursion M=1+sum r_k z^k M^k
 out=0
 def coeff(k,total):
  if k==0:return int(total==0)
  return sum(m[j]*coeff(k-1,total-j) for j in range(total+1))
 for k in range(1,n+1):out+=weights[k]*coeff(k,n-k)
 m.append(out);t=()
 for j in range(n):t=(t,)
 print(json.dumps({'N':n,'chain':f(t),'nc_ansatz':out,'equal':f(t)==out}),flush=True)
