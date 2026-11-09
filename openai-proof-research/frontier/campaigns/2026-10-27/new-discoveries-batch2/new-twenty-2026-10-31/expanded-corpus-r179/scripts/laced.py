# Baek arXiv:2206.04260 Conjecture conj:interweaved. Configuration: points 0..N-1 (linear order), each 3-set coloured cup(0)/cap(1).
# a-cup: x1<..<xa with every consecutive triple a cup (1-cups, 2-cups always). Laced (n-1)-cup from p to q: exists cup ending at p of
# size i and cup starting at q of size j with i+j=n-1. Interweaved: C1 p->r, C2 q->s with p<q<=r<s. Seek 4-cap,n-cup free
# configuration of size C(n-1,2)+k with no k mutually interweaved laced (n-1)-cups (counterexample).
import sys, random, itertools, math
from functools import lru_cache
def analyse(N,n,col):
    # col: dict (i,j,k)->0/1. Compute longest cup ending at p via edge (x,p), etc.
    # endcup[x][p] = longest cup ending with edge xp ; startcup[p][y] longest cup starting with edge py
    end=[[0]*N for _ in range(N)]; endcap=[[0]*N for _ in range(N)]
    for p in range(N):
        for x in range(p):
            b=2; bc=2
            for w in range(x):
                if col[(w,x,p)]==0: b=max(b,end[w][x]+1)
                else: bc=max(bc,endcap[w][x]+1)
            end[x][p]=b; endcap[x][p]=bc
    st=[[0]*N for _ in range(N)]
    for p in range(N-1,-1,-1):
        for y in range(N-1,p,-1):
            b=2
            for z in range(y+1,N):
                if col[(p,y,z)]==0: b=max(b,st[y][z]+1)
            st[p][y]=b
    maxcap=max([endcap[x][p] for p in range(N) for x in range(p)]+[1])
    maxcup=max([end[x][p] for p in range(N) for x in range(p)]+[1])
    Ein=[max([1]+[end[x][p] for x in range(p)]) for p in range(N)]   # longest cup ending at p
    Sout=[max([1]+[st[p][y] for y in range(p+1,N)]) for p in range(N)] # longest cup starting at p
    return end,st,maxcap,maxcup,Ein,Sout
def cups_of_size(N,col,m):
    res=[]
    def ext(seq):
        if len(seq)==m: res.append(tuple(seq)); return
        for z in range(seq[-1]+1,N):
            if len(seq)<2 or col[(seq[-2],seq[-1],z)]==0: ext(seq+[z])
    for a in range(N): ext([a])
    return res
def best_interweaved(N,n,col,Ein,Sout):
    pairs=set()
    for c in cups_of_size(N,col,n-1):
        p,q=c[0],c[-1]
        # laced: exists i+j=n-1, i,j>=1, cup size i ending at p (any i<=Ein[p]) and size j starting at q (j<=Sout[q])
        if Ein[p]+Sout[q]>=n-1: pairs.add((p,q))
    best=0
    for t in range(N):
        P=sorted(x for x in pairs if x[0]<=t<=x[1])
        # longest chain strictly increasing in both coordinates
        L=[]
        for i,(s,e) in enumerate(P):
            v=1+max([L[j] for j in range(i) if P[j][0]<s and P[j][1]<e]+[0]); L.append(v)
        best=max(best,max(L+[0]))
    return best,pairs
