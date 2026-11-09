# For each k, compute e(n)=xi2(L_n^(k)-C_n)-s2(n) for 2<=n<=N (mod 2^64 DP), then for each start n0
# find whether there exist c and 2-adic alpha (mod 2^J) consistent with all n0<=n<=N.
import sys,json
N=int(sys.argv[1]); ks=[int(x) for x in sys.argv[2].split(',')]
MASK=(1<<64)-1
def wcat_multi(blist,N):
    # run several weight sequences simultaneously (separate dp lists)
    m=len(blist); dps=[[1] for _ in range(m)]; outs=[[1] for _ in range(m)]
    for step in range(1,2*N+1):
        top=min(step,2*N-step)
        for t in range(m):
            dp=dps[t]; b=blist[t]; L=len(dp); new=[0]*(top+1)
            for h in range(top+1):
                x=dp[h-1]*b[h-1] if 1<=h<=L else 0
                if h+1<L: x+=dp[h+1]
                new[h]=x&MASK
            dps[t]=new
            if step%2==0: outs[t].append(new[0])
    return outs
def v2(x):
    x&=MASK
    return 64 if x==0 else (x&-x).bit_length()-1
bl=[[1]*(N+2)]+[[pow(2*h+1,2*k,1<<64) for h in range(N+2)] for k in ks]
outs=wcat_multi(bl,N); cat=outs[0]
def fit(e,n0):
    ns=[n for n in e if n>=n0]
    # c must equal e(n) for n in the non-alpha parity class; try both parities
    best=None
    for par in (0,1):
        cs={e[n] for n in ns if n%2!=par}
        if len(cs)!=1: continue
        c=cs.pop(); alpha=par; ok=True; j=1
        while True:
            j+=1
            cls={n%(1<<j) for n in ns if n%(1<<(j-1))==alpha%(1<<(j-1)) and e[n]-c>=j}
            others={n%(1<<j) for n in ns if n%(1<<(j-1))==alpha%(1<<(j-1)) and e[n]-c==j-1}
            # every n in class alpha mod 2^(j-1) has xi>=j-1; those with exactly j-1 must be the other class mod 2^j
            if len(cls)>1 or (cls and others and cls&others) or (len(others)>1):
                ok=False;break
            if any(e[n]-c<j-1 for n in ns if n%(1<<(j-1))==alpha%(1<<(j-1))): ok=False;break
            if not cls:
                if others: alpha=(others.pop())^(1<<(j-1))
                break
            alpha=cls.pop()
            if (1<<j)>2*N: break
        if ok: best=(c,bin(alpha),j)
    return best
for k,L in zip(ks,outs[1:]):
    e={n:v2(L[n]-cat[n])-bin(n).count('1') for n in range(2,N+1)}
    sat=[n for n in range(2,N+1) if v2(L[n]-cat[n])>=60]
    first=None
    for n0 in range(2,N//4):
        f=fit(e,n0)
        if f: first=(n0,f);break
    print(json.dumps(dict(k=k,N=N,fit_from_2=fit(e,2),first_n0_fitting=first,saturated=sat[:5])),flush=True)
