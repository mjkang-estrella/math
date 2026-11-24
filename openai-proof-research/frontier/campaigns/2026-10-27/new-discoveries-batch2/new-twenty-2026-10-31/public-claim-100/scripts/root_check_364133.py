from math import gcd
from functools import lru_cache
def pz(a,m):
    # period and zeros of U mod m with b=-1
    x,y=0,1%m; k=0; z=0
    while True:
        if x==0: z+=1
        x,y=y,(a*y-x)%m; k+=1
        if x==0 and y==1%m: return k,z
tab={(1,1):1,(1,2):2,(2,1):2,(2,2):2}
def scan(parity_ok, A, M, coprime):
    bad=[]
    for a in A:
        om={m:pz(a,m)[1] for m in range(2,M+1)}
        L={}
        for m in range(2,M+1):
            for n in range(m,M+1):
                if not parity_ok(a,m,n): continue
                if coprime and gcd(m,n)>1: continue
                l=m*n//gcd(m,n)
                if l not in L: L[l]=pz(a,l)[1]
                if om[m]>2 or om[n]>2 or L[l]!=tab[(om[n],om[m])]: bad.append((a,m,n,om[m],om[n],L[l]))
        
    return bad
A=[a for a in range(-12,13) if a not in (-2,-1,0,1,2)]
hyp=lambda a,m,n: (a%2==1) or (m%2==1 and n%2==1)
b1=scan(hyp,A,60,False); print('within 4.27 parity hypotheses, all pairs:',len(b1),b1[:8])
b2=scan(hyp,A,60,True); print('within hypotheses, coprime pairs:',len(b2),b2[:8])
b3=scan(lambda a,m,n: not hyp(a,m,n),A,40,True); print('outside hypotheses coprime:',len(b3),b3[:5])
