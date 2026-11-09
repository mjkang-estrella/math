# Smyth Conjecture 1.5 (arXiv:1512.04084): injection U^A_b x U^B_a -> U^A_a x U^B_b with lambda1mu1 dominates lambda2mu2.
# Edges depend only on sorted multisets; existence <=> type-level max flow equals |X|.
import sys,itertools,collections,json
from math import comb
def comps(n,m):
    if m==0:
        if n==0: yield ()
        return
    if m==1: yield (n,); return
    for i in range(n+1):
        for r in comps(n-i,m-1): yield (i,)+r
from math import factorial
def partitions(n,m,mx=None):
    if mx is None: mx=n
    if n==0: yield (); return
    if m==0: return
    for k in range(min(n,mx),0,-1):
        for r in partitions(n-k,m-1,k): yield (k,)+r
def parts_count(n,m):
    c=collections.Counter()
    for p in partitions(n,m):
        full=p+(0,)*(m-len(p)); mult=collections.Counter(full)
        v=factorial(m)
        for x in mult.values(): v//=factorial(x)
        c[p]+=v
    return c
def dom(p,q):  # p dominates q (same total, padded)
    L=max(len(p),len(q)); sp=sq=0
    for i in range(L):
        sp+=p[i] if i<len(p) else 0; sq+=q[i] if i<len(q) else 0
        if sp<sq: return False
    return True
def combine(c1,c2):
    c=collections.Counter()
    for p,a in c1.items():
        for q,b in c2.items():
            c[tuple(sorted(p+q,reverse=True))]+=a*b
    return c
def maxflow_ok(X,Y):
    # greedy is not enough in general; do Hall via flow (Dinic-lite with Edmonds-Karp on type graph)
    xs=list(X); ys=list(Y)
    nX=len(xs); nY=len(ys); S=0; T=1+nX+nY
    N=T+1; cap=collections.defaultdict(int); adj=[[] for _ in range(N)]
    def add(u,v,c):
        if (u,v) not in cap and (v,u) not in cap: adj[u].append(v); adj[v].append(u)
        cap[(u,v)]+=c
    INF=10**18
    for i,p in enumerate(xs): add(S,1+i,X[p])
    for j,q in enumerate(ys): add(1+nX+j,T,Y[q])
    for i,p in enumerate(xs):
        for j,q in enumerate(ys):
            if dom(p,q): add(1+i,1+nX+j,INF)
    flow=0
    while True:
        par={S:None}; dq=collections.deque([S])
        while dq and T not in par:
            u=dq.popleft()
            for v in adj[u]:
                if v not in par and cap[(u,v)]>0: par[v]=u; dq.append(v)
        if T not in par: break
        v=T; f=INF
        while par[v] is not None: u=par[v]; f=min(f,cap[(u,v)]); v=u
        v=T
        while par[v] is not None: u=par[v]; cap[(u,v)]-=f; cap[(v,u)]+=f; v=u
        flow+=f
    return flow
def sz(n,m):
    return (1 if n==0 else 0) if m==0 else comb(n+m-1,m-1)
def check(A,a,B,b):
    X=combine(parts_count(b,A),parts_count(a,B))
    Y=combine(parts_count(a,A),parts_count(b,B))
    nx=sum(X.values()); ny=sum(Y.values())
    f=maxflow_ok(X,Y)
    return nx,ny,f
if __name__=='__main__':
    M=int(sys.argv[1]); W=int(sys.argv[2])
    bad=[];cnt=0
    for A in range(0,M+1):
        for B in range(0,A+1):
            for a in range(0,W+1):
                for b in range(0,a+1):
                    if A+B==0: continue
                    if a+b>int(sys.argv[3]) if len(sys.argv)>3 else False: continue
                    nx,ny,f=check(A,a,B,b); cnt+=1
                    if f<nx: bad.append((A,a,B,b,nx,ny,f)); print('FAIL',A,a,B,b,nx,ny,f,flush=True)
    print('checked',cnt,'failures',len(bad))
