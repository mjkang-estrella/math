import math,json,time,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
mode=sys.argv[1];zeros=[];count=0;t=time.monotonic()
def S(k,n):
 lo=max(3*k,k+n);hi=2*k+n
 # term (j+1)!/((j-3k)! (j-k-n)!^3 (2k+n-j)!^3); common factorial factor immaterial
 # source integer sum binom(j+1,3k+1) binom(k,j-k-n)^3
 a=(-1)**lo*math.comb(lo+1,3*k+1)*math.comb(k,lo-k-n)**3;s=a
 for j in range(lo,hi):
  a=-a*(j+2)*(2*k+n-j)**3//((j-3*k)*(j-k-n+1)**3) if j>3*k else (-1)**(j+1)*math.comb(j+2,3*k+1)*math.comb(k,j+1-k-n)**3
  # ratio denominator j+1-3k rather than j-3k!
  # recompute below to avoid ratio ambiguity
  a=(-1)**(j+1)*math.comb(j+2,3*k+1)*math.comb(k,j+1-k-n)**3
  s+=a
 return s
if mode=='strip':
 for k in range(2,41):
  for n in range(k,5001):
   z=S(k,n);count+=1
   if not z:zeros.append([k,n]);print('zero',k,n,flush=True)
  print('k_complete',k,'count',count,flush=True)
else:
 for k in range(2,351):
  for d in range(301):
   n=k+d;z=S(k,n);count+=1
   if not z:zeros.append([k,n]);print('zero',k,n,flush=True)
  print('k_complete',k,'count',count,flush=True)
print(json.dumps({'mode':mode,'pairs':count,'zeros':zeros,'wall':time.monotonic()-t}))
