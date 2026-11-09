import math
N=24
D=[[0]*(N+1) for _ in range(N+1)]
for n in range(N+1): D[n][0]=1
for k in range(N+1): D[0][k]=1
for n in range(1,N+1):
    for k in range(1,N+1):
        D[n][k]=D[n-1][k]+D[n-1][k-1]+D[n][k-1]
print("Delannoy row1:",D[1][:5],"row2:",D[2][:5])
def durand(p,tol=1e-9,it=500):
    n=len(p)-1
    if n<1: return []
    monic=[complex(x) for x in p]; m0=monic[0]; monic=[x/m0 for x in monic]
    roots=[complex(0.4,0.9)**k*(1+0.13*k) for k in range(n)]
    for _ in range(it):
        mx=0
        for i in range(n):
            num=monic[0]
            for j in range(1,n+1): num=num*roots[i]+monic[j]
            den=1.0
            for j in range(n):
                if j!=i: den*=(roots[i]-roots[j])
            roots[i]-=num/den; mx=max(mx,abs(num/den))
        if mx<tol: break
    return roots
bad=[]
for n in range(2,N+1):
    poly=[0]*(n+1)
    for j in range(n+1):
        for k in range(min(j,n)+1):
            poly[k]+=D[n][j]*D[j][k]
    r=durand(poly[::-1])
    imag=[x for x in r if abs(x.imag)>1e-6]
    if imag: bad.append((n,len(imag)))
print("375724 D^2 rows with non-real roots n<=24:",bad[:8],"count",len(bad))
# Eulerian square for contrast
from math import comb
