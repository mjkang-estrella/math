# Independent sweep: all 7-smooth m with a*c=0 (Theorem A) and dc(m) <= DMAX.
import sys, time
from math import prod
DMAX=int(sys.argv[1]); LIM=10**DMAX
def P(n):
    k=0
    while n>=10:
        s=str(n)
        if '0' in s: return k+1
        n=prod(map(int,s)); k+=1
    return k
hist={}; front=[]; pts=0; t0=time.time()
for (p,q) in ((2,3),(5,3)):          # even family 2^a3^b7^d, five family 5^c3^b7^d
    x=1
    while x<LIM:
        y=x
        while y<LIM:
            z=y
            while z<LIM:
                pts+=1
                s=str(z)
                if '0' not in s:
                    k=P(z); hist[k]=hist.get(k,0)+1
                    if k>=10: front.append(z)
                z*=7
            y*=q
        x*=p
print(f"DMAX={DMAX} points={pts} zero-free hist={dict(sorted(hist.items()))} P>=10: {sorted(set(front))}  {time.time()-t0:.0f}s")
