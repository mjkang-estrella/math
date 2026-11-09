# 337060: enumerate C_n(1,a,b), decide arc-transitivity (= edge-transitivity for circulants), test conditions.
import sys
from math import gcd
def refine(adj,col):
    n=len(adj)
    while True:
        sig=[(col[v],tuple(sorted(col[u] for u in adj[v]))) for v in range(n)]
        keys=sorted(set(sig)); idx={k:i for i,k in enumerate(keys)}
        new=[idx[s] for s in sig]
        if len(keys)==len(set(col)): return new
        col=new
def iso_exists(adj,pairs):
    # is there an automorphism mapping pairs[i][0] -> pairs[i][1]? joint refinement on disjoint union
    n=len(adj)
    U=[list(a) for a in adj]+[[u+n for u in a] for a in adj]
    def rec(fix):
        col=[0]*(2*n)
        for k,(x,y) in enumerate(fix): col[x]=k+1; col[y+n]=k+1
        c=refine(U,col)
        from collections import Counter
        if Counter(c[:n])!=Counter(c[n:]): return False
        if len(set(c[:n]))==n:
            m={}
            inv={c[n+v]:v for v in range(n)}
            f=[inv[c[v]] for v in range(n)]
            S=set((x,y) for x in range(n) for y in adj[x])
            return all((f[x],f[y]) in S for (x,y) in S)
        # pick smallest nonsingleton cell in left
        cnt=Counter(c[:n]); cell=min((k for k in cnt if cnt[k]>1),key=lambda k:cnt[k])
        x=next(v for v in range(n) if c[v]==cell)
        for y in range(n):
            if c[n+y]==cell:
                if rec(fix+[(x,y)]): return True
        return False
    return rec(list(pairs))
def conds(n,a,b):
    pm=lambda x:x%n in (1,n-1)
    return pm(a*b),pm(a*a),pm(b*b)
N1,N2=int(sys.argv[1]),int(sys.argv[2])
out=[]
for n in range(N1,N2+1):
    seen=set()
    for a in range(2,n//2+1):
        for b in range(a+1,n//2+1):
            S=sorted(set(x%n for x in (1,-1,a,-a,b,-b)))
            if len(set(min(x,n-x) for x in S))<3: continue
            # canonical under multipliers
            units=[m for m in range(1,n) if gcd(m,n)==1]
            can=min(tuple(sorted(set(m*x%n for x in S))) for m in units)
            if can in seen: continue
            seen.add(can)
            adj=[[ (v+s)%n for s in S] for v in range(n)]
            # connected? (1 in S so yes)
            mult=[m for m in units if set(m*x%n for x in S)==set(S)]
            orb=set(m*1%n for m in mult)
            normal_trans = orb==set(S)
            if normal_trans: at=True
            else:
                at=all(iso_exists(adj,[(0,0),(1,s)]) for s in S if s not in orb)
            if at:
                c=conds(n,a,b)
                out.append((n,a,b,len(S),normal_trans,c))
                if not any(c): print("VIOLATION",n,a,b,len(S),normal_trans,flush=True)
for o in out:
    if not o[4]: print("nonnormal-AT",o)
print("total AT",len(out))
