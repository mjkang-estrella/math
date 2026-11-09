# Bounded exact computation: minimum edges of an n-vertex C5-semisaturated graph, n<=7 (n=8 partial).
# Definition (Furedi-Kim arXiv:1103.0067): G is C5-semisaturated iff adding any missing edge
# increases the number of C5 copies. Equivalently: every non-adjacent pair (u,v) is joined by a
# path of length 4 (u-x-y-z-v, 3 distinct internal vertices) -- a C5 through the new edge uv.
import itertools, sys, time
from math import comb

def semisat(adj, n):
    # adj: list of bitmasks
    full = (1<<n)-1
    for u in range(n):
        au = adj[u]
        for v in range(u+1,n):
            if au>>v & 1: continue  # edge
            av = adj[v]
            found = False
            for x in range(n):
                if x==u or x==v: continue
                if not (au>>x)&1: continue
                ax = adj[x]
                for y in range(n):
                    if y==u or y==v or y==x: continue
                    if not (ax>>y)&1: continue
                    ay = adj[y]
                    common = ay & av
                    # z adjacent to y and v, z distinct
                    common &= ~( (1<<u)|(1<<v)|(1<<x)|(1<<y) )
                    if common:
                        found=True; break
                if found: break
            if not found:
                return False
    return True

def connected_and_mindeg1(adj,n):
    if any(a==0 for a in adj): return False
    seen=0; stack=[0]; seen=1
    while stack:
        v=stack.pop()
        m=adj[v]&~seen
        while m:
            b=m&-m; m^=b; i=b.bit_length()-1
            if not (seen>>i)&1:
                seen|=1<<i; stack.append(i)
    return seen==(1<<n)-1

for n in [5,6,7]:
    edges=list(itertools.combinations(range(n),2))
    best=None; best_g=None
    t0=time.time()
    for m in range(n-1, 40):
        if best is not None: break
        cnt=0
        for es in itertools.combinations(edges,m):
            adj=[0]*n
            for a,b in es: adj[a]|=1<<b; adj[b]|=1<<a
            cnt+=1
            if connected_and_mindeg1(adj,n) and semisat(adj,n):
                best=m; best_g=es; break
        print(f"n={n} m={m}: {cnt} graphs checked, semisat found: {best}", flush=True)
        if time.time()-t0>150:
            print(f"n={n} TIME BUDGET HIT at m={m}"); break
    print(f"RESULT n={n}: ssat={best}, witness edges={best_g}", flush=True)
