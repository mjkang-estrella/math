# OPT_k(n): overpartition k-tuples with odd parts; GF = (prod (1+q^(2m-1))/(1-q^(2m-1)))^k. Check SSS congruences for k = 2^i r.
import sys
N=int(sys.argv[1])
def series_base(N):
    a=[0]*(N+1); a[0]=1
    for m in range(1,N+1,2):
        # multiply by (1+q^m)/(1-q^m) = 1 + 2 sum_{j>=1} q^{jm}
        b=a[:]
        for n in range(m,N+1):
            b[n]+=b[n-m]   # divide by (1-q^m)
        c=b[:]
        for n in range(N,m-1,-1):
            c[n]+=b[n-m]   # multiply by (1+q^m)
        a=c
    return a
def mul(a,b,N):
    c=[0]*(N+1)
    for i,x in enumerate(a):
        if x:
            for j in range(0,N+1-i):
                c[i+j]+=x*b[j]
    return c
def power(a,k,N):
    r=[1]+[0]*N; p=a
    while k:
        if k&1: r=mul(r,p,N)
        p=mul(p,p,N); k>>=1
    return r
base=series_base(N)
mods={1:lambda i:i+1,2:lambda i:2*i+1,3:lambda i:i+3,4:lambda i:2*i+4,5:lambda i:i+2,6:lambda i:2*i+3,7:lambda i:i+4}
bad=0
for i in range(1,5):
    for r in (1,3,5,7,9):
        k=2**i*r
        if k>80: continue
        s=power(base,k,N)
        for res,e in mods.items():
            for n in range(res,N+1,8):
                if s[n]%(2**e(i)):
                    v=(s[n]&-s[n]).bit_length()-1
                    print('FAIL i=%d r=%d k=%d n=%d (8n+%d) need 2^%d have 2^%d'%(i,r,k,n,res,e(i),v)); bad+=1; break
print('checked N=',N,'failures',bad)
