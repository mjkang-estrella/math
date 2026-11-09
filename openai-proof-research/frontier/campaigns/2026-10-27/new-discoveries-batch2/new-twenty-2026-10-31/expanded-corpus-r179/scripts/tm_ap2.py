# Version 2 of tm_ap.py (same exact window reduction). Stage 1: iterative exact A(d) if A(d) < 21 (K: 2^K > 20d).
# Stage 2: iterative exact A(d) if A(d) < 400 (K: 2^K > 399d). Stage 3 (A>=400): doubling tests for lengths d+5 and d+6
# with K: 2^K > (d+5)d; reports A<=d+4, A=d+5 (EQUALITY) or A>=d+6 (COUNTEREXAMPLE).
import sys, time
lo,hi=int(sys.argv[1]),int(sys.argv[2]); NO3=len(sys.argv)>3
cache={}
def tm(m):
    if m in cache: return cache[m]
    if len(cache)>3: cache.clear()
    T=0; L=1
    for j in range(m):
        T = T | (((~T) & ((1<<L)-1)) << L); L*=2
    cache[m]=T; return T
def Ms(d,K):
    x=tm(K); W1=tm(K+1); n=1<<(K+1); W2 = x | (x << (1<<K)); mask=(1<<(n-d))-1
    return [~(W^(W>>d)) & mask for W in (W1,W2)]
def iterative(d,Lcap,K):
    best=1
    for M in Ms(d,K):
        P=M; L=2
        while L<Lcap:
            Q = P & (M >> ((L-1)*d))
            if not Q: break
            P=Q; L+=1
        if P: best=max(best,L)
    return best   # exact if < Lcap
def has_len(M,d,m):  # is there i with M(i+jd)=1 for all j<m-1, i.e. AP length m
    m-=1; R=None; Pp=M; sh=1; acc=0  # Pp = P_sh
    while m:
        if m&1:
            R = Pp if R is None else (R & (Pp >> (acc*d))); acc+=sh
        m>>=1
        if m: Pp = Pp & (Pp >> (sh*d)); sh*=2
    return R!=0
t0=time.time(); res=[]
for d in range(lo|1,hi+1,2):
    A=iterative(d,21,(20*d).bit_length())
    if A<21: res.append((d,A)); continue
    A=iterative(d,400,(399*d).bit_length())
    if A<400: res.append((d,A)); print(d,A,flush=True); continue
    q=d//4+1; Mq=Ms(d,((q-1)*d).bit_length())
    if not any(has_len(M,d,q) for M in Mq): res.append((d,"<=d/4")); print(d,">=400 and <=d//4 (stage3prime)",flush=True); del Mq; continue
    del Mq
    if NO3: res.append((d,">d/4")); print(d,">d/4 stage3-skipped",flush=True); continue
    Mm=Ms(d,((d+5)*d).bit_length())
    e5=any(has_len(M,d,d+5) for M in Mm); e6=any(has_len(M,d,d+6) for M in Mm)
    tag='COUNTEREXAMPLE' if e6 else ('EQUALITY(A=d+5)' if e5 else 'A<=d+4')
    res.append((d,tag)); print(d,'>=400',tag,flush=True)
print('range',lo,hi,'odd d',len(res),'time',round(time.time()-t0,1))
