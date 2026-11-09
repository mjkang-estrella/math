import numpy as np
from fractions import Fraction
# --- 375724: real-rootedness of row polys of D^2 (Delannoy squared) ---
N=26
D=[[0]*(N+1) for _ in range(N+1)]
for n in range(N+1):
    D[n][0]=1
for n in range(1,N+1):
    for k in range(1,N+1):
        D[n][k]=D[n-1][k]+D[n-1][k-1]+D[n][k-1]
def polymul(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q): r[i+j]+=a*b
    return r
bad=[]
for n in range(1,N+1):
    # row n of D^2 = sum_j D[n][j] * row_j of D
    poly=[0]*(n+1)
    for j in range(n+1):
        row=D[j][:n+1]  # row j has entries up to k=j
        for k in range(min(j,n)+1):
            poly[k]+=D[n][j]*D[j][k]
    # roots
    r=np.roots(poly[::-1])
    if any(abs(x.imag)>1e-7 for x in r): bad.append((n,[x for x in r if abs(x.imag)>1e-7][:2]))
print("375724 D^2 non-real-root rows (n<=%d):"%N, [(n,) for n,_ in bad][:10], "count",len(bad))

# --- 371523 Bonse Psi: verify ranges numerically ---
def sieve(N):
    isp=[True]*(N+1); isp[0]=isp[1]=False
    for i in range(2,int(N**.5)+1):
        if isp[i]:
            for j in range(i*i,N+1,i): isp[j]=False
    return [i for i in range(N+1) if isp[i]]
pr=sieve(600000)
import math
# cumulative primorial log
LOG=[0.0]
for p in pr: LOG.append(LOG[-1]+math.log(p))
def pi(x): 
    import bisect; return bisect.bisect_right(pr,x)
def check(xv,mmax=4000):
    # inequality: LOG[n] > k(n,x)*log(p[n+1])  (n 1-indexed: p_1..p_n product, p_{n+1})
    fails=[]
    for n in range(8,mmax):
        k=n-pi(n)+pi(n)/pi(math.log(n))-xv*pi(pi(n))
        if LOG[n] <= k*math.log(pr[n]): fails.append(n)
    return fails
for xv,claim in [(1.3,21),(1.2,21),(1.1,21),(0.9,21),(0.8,149),(0.5,149)]:
    f=check(xv,6000)
    print("x=%s first failing n (n<4000): %s"%(xv,f[:3]))
