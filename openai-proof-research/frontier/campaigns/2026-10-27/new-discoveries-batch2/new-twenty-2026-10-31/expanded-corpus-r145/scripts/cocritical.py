# MathDB 359361 (Hanson-Toft), first case (K3,K3), r=6: minimum edges of (K3,K3)-co-critical graphs on n
# vertices vs conjectured (r-2)(n-r+2)+C(r-2,2) = 4n-10. Graphs up to isomorphism by vertex extension
# (reusing the canonical form of d2antimagic.py, copied here).
import sys,itertools,json,time
sys.setrecursionlimit(10000)
N=int(sys.argv[1])
def canon(n,adj):
    deg=[bin(a).count('1') for a in adj]
    key=[(deg[v],tuple(sorted(deg[u] for u in range(n) if adj[v]>>u&1))) for v in range(n)]
    groups={}
    for v in range(n): groups.setdefault(key[v],[]).append(v)
    order=sorted(groups); best=None
    for combo in itertools.product(*[itertools.permutations(groups[k]) for k in order]):
        perm=[v for g in combo for v in g]; pos={v:i for i,v in enumerate(perm)}
        code=tuple(sorted((min(pos[u],pos[v]),max(pos[u],pos[v])) for v in range(n) for u in range(v+1,n) if adj[v]>>u&1))
        code=(tuple(sorted(key)),code)
        if best is None or code<best: best=code
    return best
def extend(classes,n):
    out={}
    for adj in classes:
        for nb in range(1<<n):
            a=list(adj)+[nb]
            for v in range(n):
                if nb>>v&1: a[v]|=1<<n
            c=canon(n+1,a)
            if c not in out: out[c]=tuple(a)
    return list(out.values())
def has_good_coloring(n,adj):
    # 2-color edges with no monochromatic triangle (backtracking over edges; triangles checked on assignment)
    edges=[(u,v) for v in range(n) for u in range(v) if adj[v]>>u&1]
    idx={e:i for i,e in enumerate(edges)}
    tri_of=[[] for _ in edges]
    for i,(u,v) in enumerate(edges):
        common=adj[u]&adj[v]
        w=common
        while w:
            b=w&-w; w^=b; x=b.bit_length()-1
            e1=idx[(min(u,x),max(u,x))]; e2=idx[(min(v,x),max(v,x))]
            if e1<i and e2<i: tri_of[i].append((e1,e2))
    col=[0]*len(edges)
    def bt(i):
        if i==len(edges): return True
        for c in (0,1):
            if all(not(col[a]==c and col[b]==c) for a,b in tri_of[i]):
                col[i]=c
                if bt(i+1): return True
        return False
    if not edges: return True
    col[0]=0
    return bt(1)
classes=[(0,)]; t0=time.time()
for n in range(1,N):
    classes=extend(classes,n); nn=n+1
    full=(1<<nn)-1
    cocrit=[]
    for a in classes:
        nonedges=[(u,v) for v in range(nn) for u in range(v) if not a[v]>>u&1]
        if not nonedges: continue
        if not has_good_coloring(nn,a): continue
        ok=True
        for (u,v) in nonedges:
            b=list(a); b[u]|=1<<v; b[v]|=1<<u
            if has_good_coloring(nn,b): ok=False;break
        if ok: cocrit.append(a)
    es=[sum(bin(x).count('1') for x in a)//2 for a in cocrit]
    mn=min(es) if es else None
    ex=[list(a) for a,e in zip(cocrit,es) if e==mn][:3]
    print(json.dumps(dict(n=nn,classes=len(classes),cocritical=len(cocrit),min_edges=mn,conj=4*nn-10,edge_hist=sorted(set(es))[:6],min_examples=ex,sec=round(time.time()-t0,1))),flush=True)
