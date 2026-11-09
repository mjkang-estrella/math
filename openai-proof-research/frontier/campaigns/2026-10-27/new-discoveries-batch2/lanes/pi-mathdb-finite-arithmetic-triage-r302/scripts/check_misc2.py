import math
# --- 375724: real-rootedness of row polys of D^2, Durand-Kerner ---
N=24
D=[[0]*(N+1) for _ in range(N+1)]
for n in range(N+1): D[n][0]=1
for n in range(1,N+1):
    for k in range(1,N+1):
        D[n][k]=D[n-1][k]+D[n-1][k-1]+D[n][k-1]
def durand(p,tol=1e-9,it=300):
    n=len(p)-1
    if n<1: return []
    c=[complex(x) for x in p]
    monic=[x/c[0] for x in c]
    roots=[complex(0.4,0.9)**k*(1+0.1*k) for k in range(n)]
    for _ in range(it):
        mx=0
        for i in range(n):
            num=monic[0]
            for j in range(1,n+1): num=num*roots[i]+monic[j]
            den=1.0
            for j in range(n):
                if j!=i: den*= (roots[i]-roots[j])
            step=num/den
            roots[i]-=step; mx=max(mx,abs(step))
        if mx<tol: break
    return roots
bad=[]
for n in range(1,N+1):
    poly=[0]*(n+1)
    for j in range(n+1):
        for k in range(min(j,n)+1):
            poly[k]+=D[n][j]*D[j][k]
    poly=[x for x in poly]
    while len(poly)>1 and poly[-1]==0: poly.pop()
    r=durand(poly[::-1])
    imag=[x for x in r if abs(x.imag)>1e-6]
    if imag: bad.append((n,len(imag)))
print("375724 rows of D^2 with non-real roots (n<=24):",bad,"count",len(bad))

# --- 371523 Bonse Psi ranges ---
def sieve(N):
    isp=bytearray([1])*(N+1); isp[0]=isp[1]=0
    for i in range(2,int(N**.5)+1):
        if isp[i]:
            for j in range(i*i,N+1,i): isp[j]=0
    return [i for i in range(N+1) if isp[i]]
pr=sieve(700000)
LOG=[0.0]
for p in pr: LOG.append(LOG[-1]+math.log(p))
import bisect
def pi(x): return bisect.bisect_right(pr,x)
def fails(xv,mmax=5000):
    out=[]
    for n in range(8,mmax):
        k=n-pi(n)+pi(n)/pi(math.log(n))-xv*pi(pi(n))
        if LOG[n] <= k*math.log(pr[n]): out.append(n)
    return out
for xv in [1.3,1.2,1.1,0.9]:
    f=fails(xv); print("x=%s first fails n<5000: %s"%(xv,f[:4]))
for xv in [0.8,0.5]:
    f=fails(xv); print("x=%s first fails n<5000: %s"%(xv,f[:4]))
