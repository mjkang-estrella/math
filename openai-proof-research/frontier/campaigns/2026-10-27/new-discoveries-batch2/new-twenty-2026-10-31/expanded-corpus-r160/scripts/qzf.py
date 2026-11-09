# Exact Z_q game value (Butler-Grout-Hall q-analogue of zero forcing), as defined in arXiv:2306.01138 Sec.1.
# Op1: token colours any vertex (cost 1). Op2: CCR on G (one force, free). Op3: if white comps k>=q+1, player
# selects >=q+1 comps T, oracle picks nonempty S subset T, player applies one CCR force in G[B u S] (free).
# An op3 selection where some oracle answer allows no force is useless (state unchanged) and is ignored.
import sys, itertools
from functools import lru_cache
sys.setrecursionlimit(10000)
def solve(N, adj, q):
    FULL=(1<<N)-1
    nb=adj
    def comps(W):
        res=[]
        while W:
            v=W & -W; c=v; fr=v
            while fr:
                x=fr & -fr; fr^=x; i=x.bit_length()-1
                new=nb[i] & W & ~c; c|=new; fr|=new
            res.append(c); W&=~c
        return res
    def forces(B, allowedW):
        # vertices w in allowedW forced by some u in B whose white nbrs within allowedW = {w}
        out=0
        b=B
        while b:
            x=b & -b; b^=x; u=x.bit_length()-1
            wn=nb[u] & allowedW
            if wn and (wn & (wn-1))==0: out|=wn
        return out
    memo={}
    def cost(B):
        if B==FULL: return 0
        r=memo.get(B)
        if r is not None: return r
        W=FULL & ~B
        best=10**9
        f=forces(B,W)
        ff=f
        while ff:
            x=ff & -ff; ff^=x
            best=min(best,cost(B|x))
            if best==0: break
        if best>0:
            C=comps(W); k=len(C)
            if k>=q+1:
                # selection T of >=q+1 comps; oracle answer S nonempty subset of T
                # value(S) = min over forces available in G[B u S] ; inf if none
                sval={}
                for mask in range(1,1<<k):
                    U=0
                    for i in range(k):
                        if mask>>i &1: U|=C[i]
                    fs=forces(B,U)
                    if not fs: sval[mask]=None; continue
                    v=10**9; t=fs
                    while t:
                        x=t & -t; t^=x; v=min(v,cost(B|x))
                    sval[mask]=v
                for T in range(1,1<<k):
                    if bin(T).count('1')<q+1: continue
                    worst=-1; ok=True
                    S=T
                    while S:
                        sv=sval[S]
                        if sv is None: ok=False; break
                        if sv>worst: worst=sv
                        if worst>=best: break
                        S=(S-1)&T
                    if ok and worst<best: best=worst
            if best>0:
                w=W
                while w:
                    x=w & -w; w^=x
                    c=1+cost(B|x)
                    if c<best: best=c
        memo[B]=best
        return best
    return cost(0), len(memo)

def graph_Knm_K2(n,m):
    # layer a: X 0..n-1, Y n..n+m-1 ; layer b: +n+m
    N=2*(n+m); adj=[0]*N
    def e(u,v): adj[u]|=1<<v; adj[v]|=1<<u
    for L in (0,n+m):
        for i in range(n):
            for j in range(m): e(L+i,L+n+j)
    for v in range(n+m): e(v,v+n+m)
    return N,adj
def graph_Knm(n,m):
    N=n+m; adj=[0]*N
    for i in range(n):
        for j in range(m): adj[i]|=1<<(n+j); adj[n+j]|=1<<i
    return N,adj
def graph_book(n): return graph_Knm_K2(1,n)
if __name__=='__main__':
    import time
    mode=sys.argv[1]; a=int(sys.argv[2]); b=int(sys.argv[3]); qs=[int(x) for x in sys.argv[4].split(',')]
    G={'knmk2':graph_Knm_K2,'knm':graph_Knm}[mode](a,b)
    for q in qs:
        t=time.time(); v,s=solve(*G,q); print(mode,a,b,'q=',q,'Z_q=',v,'states',s,'sec',round(time.time()-t,1),flush=True)
