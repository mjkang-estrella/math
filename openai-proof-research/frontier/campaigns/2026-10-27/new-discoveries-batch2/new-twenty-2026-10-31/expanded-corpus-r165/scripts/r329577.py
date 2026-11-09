from fractions import Fraction as F
from math import comb, gcd
import sys
N=int(sys.argv[1])
def lcm(a,b): return a*b//gcd(a,b)
for r in range(0,8):
    R=[sum(F(comb(n+k,2*k)*comb(2*k,k),2*k-2*r-1) for k in range(n+1)) for n in range(N)]
    S=F(0); L=1; hist=[]
    for n in range(1,N+1):
        S+=(2*n-1)*R[n-1]**2
        d=(S/n).denominator
        L=lcm(L,d)
        if n in (10,20,40,N) : hist.append((n,L))
    print('r',r,hist,flush=True)
