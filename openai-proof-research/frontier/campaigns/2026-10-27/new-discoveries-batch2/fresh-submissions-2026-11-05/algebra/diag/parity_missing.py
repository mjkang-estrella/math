# M_e(n)-M_o(n) via F(q)=1+sum_L q^L prod_{j<L}(2q^j-1)/(q;q)_L, exact integers, plus brute-force check for small n.
import sys
N=int(sys.argv[1])
def mul(a,b):
    r=[0]*(N+1)
    for i,x in enumerate(a):
        if x:
            for j in range(0,N+1-i):
                if b[j]: r[i+j]+=x*b[j]
    return r
def inv_one_minus(k): # 1/(1-q^k)
    r=[0]*(N+1)
    for i in range(0,N+1,k): r[i]=1
    return r
F=[0]*(N+1); F[0]=1
P=[0]*(N+1); P[0]=1  # running prod_{j<L}(2q^j-1)/(q;q)_{L-1}
for L in range(1,N+1):
    # multiply by 1/(1-q^L) and q^L
    P=mul(P,inv_one_minus(L))
    T=[0]*(N+1)
    for i in range(N+1-L): T[i+L]=P[i]
    F=[F[i]+T[i] for i in range(N+1)]
    # update P *= (2q^L-1)
    Q=[-x for x in P]
    for i in range(N+1-L): Q[i+L]+=2*P[i]
    P=Q
# brute force small
def parts(n,m=None):
    if m is None:m=n
    if n==0: yield []; return
    for k in range(min(n,m),0,-1):
        for p in parts(n-k,k): yield [k]+p
for n in range(1,26):
    s=0
    for p in parts(n):
        miss=max(p)-len(set(p)); s+=(-1)**miss
    assert s==F[n],(n,s,F[n])
neg=[n for n in range(N+1) if F[n]<=0]
print('nonpositive n:',neg)
print([F[n] for n in range(0,60)])
print('ratio samples', [(n,F[n]) for n in (100,200,300,N) if n<=N])
