import math,json,time
s=time.monotonic()
# Source Proposition 4.1, exact integer arithmetic; no geometry assumed by this diagnostic.
limit=10000000
a=bytearray([0,1,2]);e=0;first=None
for i in range(limit):
 x=a[i];a.extend([2]*(4-x));a.append(3);e+=x;n=i+1
 D=5*n*n+60*n-16
 z=7*n-2*e
 # e <= bound < e+1 iff z >= sqrt(D) > z-2.
 if not (z>=0 and z*z>=D and (z-2<0 or (z-2)*(z-2)<D)):
  first=dict(n=n,spiral_edges=e,D=D,z=z,z_squared=z*z,upper_floor=(7*n-math.isqrt(D)-1)//2 if math.isqrt(D)**2!=D else (7*n-math.isqrt(D))//2)
  print(json.dumps(first),flush=True);break
 if n in [366536,1000000,10000000]:print(json.dumps(dict(checked=n,seconds=time.monotonic()-s,bytes=len(a))),flush=True)
print(json.dumps(dict(first_mismatch=first,completed=n,seconds=time.monotonic()-s)),flush=True)
