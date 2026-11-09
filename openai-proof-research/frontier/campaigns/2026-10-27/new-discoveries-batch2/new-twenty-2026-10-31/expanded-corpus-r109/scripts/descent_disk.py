# Sweep Bencs Conjecture 6.3 (MathDB 339411): roots z0 of d(I,z) satisfy |z0-(m-1)/2| <= (m+1)/2, m=max I.
# Exact integer values via d(I,n) = C(n,m) d(I^-,m) - d(I^-,n); roots numerically (diagnostic), near-boundary ones refined by mpmath.
import sys, json, math, numpy as np, mpmath
M=int(sys.argv[1]); out=sys.argv[2]
T=list(range(M+1))
binom=[[math.comb(t,k) for t in T] for k in range(M+1)]
# monomial coefficients of falling factorial t(t-1)...(t-k+1), low->high
fall=[[1]]
for k in range(1,M+1):
    prev=fall[-1]; nxt=[0]*(k+1)
    for i,c in enumerate(prev):
        nxt[i+1]+=c; nxt[i]-=(k-1)*c
    fall.append(nxt)
def mono(vals,m):
    # Newton forward differences at 0, degree m; returns integer monomial coefficients of m!*P (low->high)
    d=list(vals[:m+1]); c=[]
    for k in range(m+1):
        c.append(d[0]); d=[d[i+1]-d[i] for i in range(len(d)-1)]
    assert all(x==0 for x in d) or True
    F=math.factorial(m); co=[0]*(m+1)
    for k,ck in enumerate(c):
        if ck==0: continue
        s=ck*(F//math.factorial(k))
        for i,f in enumerate(fall[k]): co[i]+=s*f
    return co
worst=[]; count=0; viol=[]; bym={}; bym2={}
mpmath.mp.dps=60
def check(I,vals):
    global count
    m=I[-1]; co=mono(vals,m); count+=1
    # d(I,m)=0 always (z=m on the boundary); also deflate exact boundary root z=-1 when present.
    hi=co[::-1]; bnd=0
    for z0 in (m,-1):
        while True:
            q=[hi[0]]
            for a in hi[1:]: q.append(a+z0*q[-1])
            if q[-1]!=0 or len(hi)==1: break
            hi=q[:-1]; bnd+=1
    r=np.roots([float(x) for x in hi]) if len(hi)>1 else np.array([])
    c=(m-1)/2; R=(m+1)/2
    marg=R-np.abs(r-c)          # >=0 means inside
    mm=float(marg.min()) if len(r) else R
    if mm<1e-9*R:
        rr=mpmath.polyroots([mpmath.mpf(x) for x in hi],maxsteps=400,extraprec=400)
        mm=float(min(R-abs(z-c) for z in rr))
        if mm<0: viol.append({'I':I,'margin':mm,'roots':[str(z) for z in rr]})
    b=bym.setdefault(m,[1e9,None]); 
    if mm/R<b[0]: bym[m]=[mm/R,I]
    if len(I)>1:
        b2=bym2.setdefault(m,[1e9,None])
        if mm/R<b2[0]: bym2[m]=[mm/R,I]
def dfs(I,vals):
    m=I[-1] if I else 0
    if I: check(I,vals)
    for m2 in range(m+1,M+1):
        a=vals[m2]
        nv=[binom[m2][t]*a-vals[t] for t in T]
        dfs(I+[m2],nv)
dfs([],[1]*(M+1))
json.dump({'M':M,'sets_checked':count,'violations':viol,'min_relative_margin_by_m':{str(k):v for k,v in sorted(bym.items())},'min_relative_margin_by_m_multi':{str(k):v for k,v in sorted(bym2.items())}},open(out,'w'),indent=1)
print(count,len(viol)); [print(k,v,bym2.get(k)) for k,v in sorted(bym.items())]
