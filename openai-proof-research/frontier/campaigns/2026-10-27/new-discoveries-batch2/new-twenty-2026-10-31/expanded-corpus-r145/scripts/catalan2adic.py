# Test Gao-Gu Conjecture 4.12 (MathDB 343469): xi2(L_n^(k) - C_n) = s2(n) + xi2(n - alpha_k) + c_k for n>=2.
# L_n^(k) = weighted Catalan with b(h)=(2h+1)^(2k), weight b(h) per up-step from height h. Computed mod 2^64.
import sys,json
N=int(sys.argv[1]); ks=[int(x) for x in sys.argv[2].split(',')]
def wcat(bvals,N):
    MASK=(1<<64)-1
    dp=[1]; out=[1]
    for step in range(1,2*N+1):
        top=min(step,2*N-step)
        new=[0]*(top+1)
        L=len(dp)
        for h in range(top+1):
            x=0
            if h>=1 and h-1<L: x=dp[h-1]*bvals[h-1]
            if h+1<L: x+=dp[h+1]
            new[h]=x&MASK
        dp=new
        if step%2==0: out.append(dp[0])
    return out
def v2(x):
    x&=(1<<64)-1
    if x==0: return 64
    return (x&-x).bit_length()-1
M=1<<64
cat=wcat([1]*(N+2),N)
res={}
for k in ks:
    bv=[pow(2*h+1,2*k,M) for h in range(N+2)]
    L=wcat(bv,N)
    e={n: v2((L[n]-cat[n])%M)-bin(n).count('1') for n in range(2,N+1)}
    big=[n for n in e if v2((L[n]-cat[n])%M)>=60]
    c=min(e.values())
    # determine alpha bits: alpha mod 2^j is the unique class r with e(n)-c>=j for n=r mod 2^j
    alpha=0; ok=True; bad=None
    for j in range(1,40):
        cls=sorted({n%(1<<j) for n in e if e[n]-c>=j})
        # residues consistent with alpha mod 2^(j-1)
        if len(cls)>1 or (cls and cls[0]%(1<<(j-1))!=alpha):
            ok=False; bad=(j,cls[:6]); break
        if not cls: break
        alpha=cls[0]
    # full check
    def xi(n,a,j):
        d=n-a; t=0
        while t<j and d%2==0: d//=2; t+=1
        return t
    viol=[n for n in e if (e[n]-c)!=xi(n,alpha,40) and e[n]-c<j-1] if ok else None
    res[k]=dict(c=c,ok=ok,bad=bad,alpha_bits=bin(alpha),saturated=big[:5],first_e=[e[n] for n in range(2,40)])
    print(k,res[k],flush=True)
