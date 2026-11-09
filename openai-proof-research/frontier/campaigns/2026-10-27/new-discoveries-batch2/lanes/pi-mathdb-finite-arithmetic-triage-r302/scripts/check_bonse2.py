import math,bisect
def sieve(N):
    isp=bytearray([1])*(N+1); isp[0]=isp[1]=0
    for i in range(2,int(N**.5)+1):
        if isp[i]:
            for j in range(i*i,N+1,i): isp[j]=0
    return [i for i in range(N+1) if isp[i]]
pr=sieve(800000)
LOG=[0.0]
for p in pr: LOG.append(LOG[-1]+math.log(p))
def pi(x): return bisect.bisect_right(pr,x)
def fails(xv,mmax=6000):
    out=[]
    for n in range(8,mmax):
        k=n-pi(n)+pi(n)/pi(math.log(n))-xv*pi(pi(n))
        if LOG[n] <= k*math.log(pr[n]): out.append(n)
    return out
for lo,hi,claim in [(0.9,1.3,21),(0.5,0.8,149),(0.3,0.4,59875)]:
    for xv in [lo,hi]:
        f=fails(xv)
        mx=max(f) if f else 0
        print("x=%s: fails<%d: count=%d, max failing n=%s, claim Psi=%s -> %s"%(xv,6000,len(f),mx,claim,"CONSISTENT" if mx<claim else "VIOLATION"))
