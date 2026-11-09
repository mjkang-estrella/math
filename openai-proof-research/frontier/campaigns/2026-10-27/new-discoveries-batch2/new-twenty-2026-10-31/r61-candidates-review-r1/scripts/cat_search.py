# Exhaustive search (reviewer) for caterpillars violating the EXISTENTIAL reading
# ("some maximum r-centre is a leaf whose neighbour has maximum degree") with 3 <= r <= mu/2.
# Spine leaf-count tuples with nonzero ends (canonical up to the end-leaf absorption), up to reversal.
# Usage: cat_search.py NMIN NMAX [rmin]
import sys,itertools
RM=12
def mul(a,b):
    c=[0]*min(RM+1,len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x==0: continue
        for j,y in enumerate(b):
            if i+j>RM: break
            c[i+j]+=x*y
    return c
def add(a,b):
    m=max(len(a),len(b));return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(m)]
from math import comb
BIN=[[comb(a,i) for i in range(min(a,RM)+1)] for a in range(80)]
def stars(a):
    k=len(a)
    # prefix: Pin[j],Pout[j] for spine v0..vj with vj in / out
    Pin=[None]*k;Pout=[None]*k
    for j in range(k):
        if j==0: Pin[0]=[0,1];Pout[0]=BIN[a[0]]
        else:
            Pin[j]=mul([0,1],Pout[j-1]);Pout[j]=mul(BIN[a[j]],add(Pin[j-1],Pout[j-1]))
    Sin=[None]*k;Sout=[None]*k
    for j in range(k-1,-1,-1):
        if j==k-1: Sin[j]=[0,1];Sout[j]=BIN[a[j]]
        else:
            Sin[j]=mul([0,1],Sout[j+1]);Sout[j]=mul(BIN[a[j]],add(Sin[j+1],Sout[j+1]))
    one=[1]
    P=lambda j: one if j<0 else add(Pin[j],Pout[j])
    S=lambda j: one if j>=k else add(Sin[j],Sout[j])
    # forest after deleting v_i and N(v_i): prefix up to i-2, free leaves of v_{i-1}, same on right
    spine=[]
    leaf=[]
    for i in range(k):
        L=P(i-2); 
        if i-1>=0: L=mul(L,BIN[a[i-1]])
        R=S(i+2)
        if i+1<k: R=mul(R,BIN[a[i+1]])
        spine.append(mul(L,R))
        leaf.append(mul(mul(P(i-1),S(i+1)),BIN[a[i]-1]) if a[i]>0 else None)
    return spine,leaf
def mu(a):
    k=len(a);INF=10**9
    # state: (prev in S?, prev dominated?) ; process spine
    # dp over i with states (in_i, dominated_i)
    dp={}
    dp[(1,1)]=1; dp[(0,1 if a[0]>0 else 0)]=a[0]
    for i in range(1,k):
        nd={}
        for (pin,pdom),c in dp.items():
            # v_i in S
            if not pin:
                key=(1,1);nd[key]=min(nd.get(key,INF),c+1)  # prev now dominated
            # v_i out
            if pin or pdom:
                dom=1 if (pin or a[i]>0) else 0
                key=(0,dom);nd[key]=min(nd.get(key,INF),c+a[i])
        # fix previous-domination for v_i in S case: prev with pdom=0 becomes dominated (handled)
        dp=nd
    return min(c for (pin,pdom),c in dp.items() if pin or pdom)
ANY=len(sys.argv)>5 and sys.argv[5]=='any'
def check(a,rmin):
    m=mu(a)
    if not ANY and 2*rmin>m: return None
    k=len(a);deg=[a[i]+(i>0)+(i<k-1) for i in range(k)];D=max(deg)
    sp,lf=stars(a)
    out=[]
    for r in range(rmin,(min(m//2,RM+1) if not ANY else min(sum(a)+len(a),RM+1))+1):
        g=lambda p: p[r-1] if p is not None and r-1<len(p) else 0
        vals=[g(p) for p in sp]+[g(p) for p in lf if p is not None]
        mx=max(vals)
        if mx==0: continue
        good=any(lf[i] is not None and g(lf[i])==mx and deg[i]==D for i in range(k))
        if not good: out.append((r,m))
    return out
def comps(k,s):
    if k==0:
        if s==0: yield ()
        return
    for x in range(s+1):
        for t in comps(k-1,s-x): yield (x,)+t
def tuples(k,s):
    if k==1:
        yield (s,);return
    for x in range(1,s):
        for y in range(1,s-x+1):
            for mid in comps(k-2,s-x-y): yield (x,)+mid+(y,)
def tuples_old(k,s):
    # positive ends, nonneg middle, sum s
    if k==1:
        yield (s,);return
    for x in range(1,s):
        for y in range(1,s-x+1):
            rest=s-x-y
            if k==2:
                if rest==0: yield (x,y)
                continue
            for mid in itertools.product(range(rest+1),repeat=k-2):
                if sum(mid)==rest: yield (x,)+mid+(y,)
nmin,nmax=int(sys.argv[1]),int(sys.argv[2]);rmin=int(sys.argv[3]) if len(sys.argv)>3 else 3;KMAX=int(sys.argv[4]) if len(sys.argv)>4 else 10**9
for n in range(nmin,nmax+1):
    found=0;tested=0
    for k in range(1,min(n,KMAX+1)):
        s=n-k
        if k>=2 and s<2: continue
        for a in tuples(k,s):
            if a>a[::-1]: continue
            tested+=1
            res=check(a,rmin)
            if res: found+=1; print('FAIL',n,a,res,flush=True)
    print('n',n,'tested',tested,'failures',found,flush=True)
