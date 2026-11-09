# 325257 (Erickson-Ruskey Conjecture 2): exact P_n(z) = VH_n(z) / D_n(z) from the source Theorem 1 and Theorem 3:
#   VH_n = 2 sum_{i=1}^{floor((n-1)/2)} S_{n-i-2} S_{i-1} z^{n-i-1} + S_{floor((n-2)/2)}^2,
#   D_n  = prod_{j>=1} S_{floor((n-2)/2^j)},   S_m = prod_{t=1}^m (1+z^t).
# N = None: full polynomials; N = int: everything truncated mod z^N (exact for coefficients < N).
import sys, json
def mul1(p,t,N):  # p*(1+z^t)
    L=len(p)+t if N is None else min(len(p)+t,N)
    q=p+[0]*(L-len(p)) if L>=len(p) else p[:L]
    for k in range(L-1,t-1,-1):
        if k-t < len(p): q[k]+=p[k-t]
    return q
def div1(p,t):    # exact division by (1+z^t) (truncation-compatible)
    q=list(p)
    for k in range(t,len(q)): q[k]-=q[k-t]
    return q
def S(m,N):
    p=[1]
    for t in range(1,m+1): p=mul1(p,t,N)
    return p
def addto(acc,p,shift,c,N):
    L=len(p)+shift if N is None else min(len(p)+shift,N)
    if len(acc)<L: acc.extend([0]*(L-len(acc)))
    for k in range(len(p)):
        if N is not None and k+shift>=N: break
        acc[k+shift]+=c*p[k]
def VH(n,N=None):
    acc=[]
    T=S(n-3,N)               # i=1: S_{n-3} S_0
    top=(n-1)//2
    for i in range(1,top+1):
        addto(acc,T,n-i-1,2,N)
        if i<top:             # T_{i+1} = T_i (1+z^i) / (1+z^{n-i-2})
            T=mul1(T,i,N); T=div1(T,n-i-2)
            if N is None:
                while len(T)>1 and T[-1]==0: T.pop()
    s=S((n-2)//2,N)
    sq=[0]
    # square via repeated factor multiplication: S_m^2 = prod (1+z^t)^2
    sq=[1]
    for t in range(1,(n-2)//2+1): sq=mul1(mul1(sq,t,N),t,N)
    addto(acc,sq,0,1,N)
    return acc
def P(n,N=None):
    p=VH(n,N); j=1
    while (n-2)>>j:
        m=(n-2)>>j
        for t in range(1,m+1): p=div1(p,t)
        j+=1
    if N is None:
        while len(p)>1 and p[-1]==0: p.pop()
    return p
def nu(x): return bin(x).count('1')
def od(k):
    while k%2==0: k//=2
    return k
if __name__=='__main__':
    tab={3:[1,2],4:[1,1,2],5:[1,1,2,4,0,2],6:[1,0,1,2,2,-2,2],7:[1,0,1,2,2,4,-2,4,0,2,-2,2],
         11:[1,-1,1,0,1,1,1,2,2,4,-8,10,-4,10,-8,8,-8,10,-10,12,-8,10,-12,10,-6,6,-6,6,-4,4,-4,2]}
    for n,c in tab.items(): assert P(n)==c,(n,P(n))
    pm1=[1,-1,2,-4,6,-14,20,-48,70,-166,252,-584,924,-2092,3432,-7616,12870,-28102,48620,-104824,184756,-394404,705432,-1494240,2704156,-5692636,10400600]
    ab=[1,3,4,10,10,22,28,64,76,180,260,606,932,2124,3440,7666,12872,28178,48620,104946,184756,394638,705432,1494600,2704156,5693376,10400600]
    for idx,n in enumerate(range(2,29)):
        p=P(n)
        assert p and sum(p)==n*2**(nu(n-2)-1), n
        assert len(p)-1==sum(od(k) for k in range(1,n-1)), n
        assert sum(c*(-1)**k for k,c in enumerate(p))==pm1[idx], n
        assert sum(abs(c) for c in p)==ab[idx], n
    print('validated against source Table 4, P_n(1), deg P_n, P_n(-1) and abs-sum lists for n<=28')
