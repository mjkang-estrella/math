from fractions import Fraction as Q
from math import isqrt

def flsqrt(q):return isqrt(q.numerator//q.denominator)
def narrow(intervals,n):
 out=[]
 for lo,hi in intervals:
  pts={lo,hi}
  # all jumps of floor(a²n), floor(an), floor(a floor(an)).
  for j in range(int(lo*n),int(hi*n)+2):
   q=Q(j,n)
   if lo<q<hi:pts.add(q)
  for k in range(flsqrt(lo*n*n),flsqrt(hi*n*n)+2):
   q=Q(k*k,n*n)
   if lo<q<hi:pts.add(q)
   if k>0:
    for j in range(flsqrt(lo*k*k),flsqrt(hi*k*k)+2):
     q=Q(j*j,k*k)
     if lo<q<hi:pts.add(q)
  ss=sorted(pts)
  for x,y in zip(ss,ss[1:]):
   q=(x+y)/2;k=flsqrt(q*n*n)
   val=int(q*n)-flsqrt(q*k*k)
   if val==1:
    if out and out[-1][1]==x:out[-1]=(out[-1][0],y)
    else:out.append((x,y))
 return out
if __name__ == '__main__':
 intervals=[(Q(1),Q(4))]
 for n in range(1,300):
  new=narrow(intervals,n)
  if new!=intervals:print(n,[(str(a),str(b)) for a,b in new])
  intervals=new
