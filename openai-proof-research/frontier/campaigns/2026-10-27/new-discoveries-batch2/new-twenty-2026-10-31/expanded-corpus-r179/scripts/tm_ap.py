# Exact A_t(d) (max monochromatic AP length of difference d anywhere in Thue-Morse t) for odd d in [lo,hi].
# Any AP of span < 2^K lies in t[q2^K,(q+2)2^K) = (t(q)^x)(t(q+1)^x), x=t[0,2^K); since 00 and 01 both occur in t,
# the candidate windows are x+xbar (=t[0,2^{K+1})) and x+x (complements irrelevant: monochromatic is colour-free).
# Stage 1: K with 2^K > 20d decides whether A(d) <= 20 (exactly).  Stage 2: K with 2^K > (d+5)d decides A(d) <= d+5 (exactly).
import sys, time
lo,hi=int(sys.argv[1]),int(sys.argv[2])
cache={}
def tm(m):  # int with bit i = t(i), i < 2^m
    if m in cache: return cache[m]
    if len(cache)>3: cache.clear()
    T=0; L=1; T=0  # t(0)=0
    for j in range(m):
        T = T | (((~T) & ((1<<L)-1)) << L); L*=2
    cache[m]=T; return T
def windows(K):
    x=tm(K); W1=tm(K+1); W2 = x | (x << (1<<K)); return [W1,W2], 1<<(K+1)
def maxlen(d, Lcap, K):
    """max L<=Lcap such that a monochromatic AP of length L exists in a window (exact if 2^K>(Lcap-1)*d); returns (Lmax, start, word index)"""
    best=(1,None,None)
    Ws,n=windows(K)
    for wi,W in enumerate(Ws):
        M = ~(W ^ (W>>d)) & ((1<<(n-d))-1)
        P=M; L=2
        while P and L<Lcap:
            Q = P & (M >> ((L-1)*d))
            if not Q: break
            P=Q; L+=1
        if P and L>best[0]:
            best=(L,(P & -P).bit_length()-1,wi)
    return best
t0=time.time(); out=[]
for d in range(lo|1, hi+1, 2):
    K=(20*d).bit_length()
    L,s,wi=maxlen(d,21,K)
    if L<21:
        out.append((d,L,'stage1')); continue
    K=((d+5)*d).bit_length()
    L,s,wi=maxlen(d,d+6,K)
    flag = 'COUNTEREXAMPLE' if L>=d+6 else ('EQUALITY' if L==d+5 else '')
    out.append((d,L,'stage2',s,wi,flag))
    print(d,L,'stage2 start',s,'word',wi,flag,flush=True)
mx=max(out,key=lambda r:r[1]-r[0])
print('range',lo,hi,'odd d checked',len(out),'max A-d',mx[1]-mx[0],'at d',mx[0],'time',round(time.time()-t0,1))
print('d with A>=21:',[(r[0],r[1]) for r in out if r[1]>=21])
