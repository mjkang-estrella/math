# Small-instance search for Fan's conjecture (arXiv:1910.09999 Conj 1.1): every flow-admissible
# signed graph has a family of signed circuits covering each edge exactly 6 times.
# Simple graphs on <= nmax vertices, all signatures up to switching (spanning-forest edges positive).
import sys, itertools, time
from functools import lru_cache
nmax=int(sys.argv[1]); nmin=int(sys.argv[2]) if len(sys.argv)>2 else 3
CH=int(sys.argv[3]) if len(sys.argv)>3 else 1; CI=int(sys.argv[4]) if len(sys.argv)>4 else 0
def graphs(n):
    pairs=list(itertools.combinations(range(n),2)); seen=set(); perms=list(itertools.permutations(range(n)))
    for mask in range(1<<len(pairs)):
        E=[pairs[i] for i in range(len(pairs)) if mask>>i&1]
        key=min(tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in E)) for p in perms)
        if key in seen: continue
        seen.add(key); yield E
def cycles(n,E):
    adj={v:[] for v in range(n)}
    for i,(a,b) in enumerate(E): adj[a].append((b,i)); adj[b].append((a,i))
    res=set()
    for s in range(n):
        # cycles whose min vertex is s
        def dfs(v,vis,es):
            for w,i in adj[v]:
                if w==s and len(es)>=2 and i not in es:
                    res.add((frozenset(es|{i}),frozenset(vis)))
                elif w>s and w not in vis:
                    dfs(w,vis|{w},es|{i})
        dfs(s,frozenset([s]),frozenset())
    return list(res)
def paths(n,E,A,B,forbid):
    # simple paths from a vertex of A to a vertex of B, internal vertices outside A|B; return edge sets
    adj={v:[] for v in range(n)}
    for i,(a,b) in enumerate(E): adj[a].append((b,i)); adj[b].append((a,i))
    out=[]
    for s in A:
        def dfs(v,vis,es):
            for w,i in adj[v]:
                if w in B: out.append(frozenset(es|{i}))
                elif w not in A and w not in vis: dfs(w,vis|{w},es|{i})
        dfs(s,{s},frozenset())
    return out
def signed_circuits(n,E,neg):
    cyc=cycles(n,E); bal=[]; unb=[]
    for es,vs in cyc:
        (bal if sum(1 for i in es if i in neg)%2==0 else unb).append((es,vs))
    sc=set(es for es,vs in bal)
    for (e1,v1),(e2,v2) in itertools.combinations(unb,2):
        inter=v1&v2
        if len(inter)==1 and not (e1&e2): sc.add(e1|e2)
        elif not inter:
            for p in paths(n,E,v1,v2,None): sc.add(e1|e2|p)
    return [tuple(sorted(c)) for c in sc]
def has_cover(m,circs,k):
    inc=[[c for c in circs if e in c] for e in range(m)]
    @lru_cache(maxsize=None)
    def go(res):
        if not any(res): return True
        e=min((i for i in range(m) if res[i]>0), key=lambda i:(sum(1 for c in inc[i] if all(res[j]>0 for j in c)),i))
        for c in inc[e]:
            if all(res[j]>0 for j in c):
                r=list(res)
                for j in c: r[j]-=1
                if go(tuple(r)): return True
        return False
    return go(tuple([k]*m))
t0=time.monotonic()
for n in range(nmin,nmax+1):
    tested=0; fa=0
    for gi,E in enumerate(graphs(n)):
        m=len(E)
        if m==0 or gi%CH!=CI: continue
        # spanning forest
        par=list(range(n))
        def f(x):
            while par[x]!=x: x=par[x]
            return x
        tree=[]
        for i,(a,b) in enumerate(E):
            ra,rb=f(a),f(b)
            if ra!=rb: par[ra]=rb; tree.append(i)
        non=[i for i in range(m) if i not in tree]
        for sm in range(1<<len(non)):
            neg=frozenset(non[j] for j in range(len(non)) if sm>>j&1)
            sc=signed_circuits(n,E,neg)
            covered=set(i for c in sc for i in c)
            if len(covered)<m: continue  # not flow-admissible
            fa+=1
            ok=has_cover(m,sc,2) or has_cover(m,sc,3) or has_cover(m,sc,6)
            if not ok: print('NO 6-COVER',n,E,sorted(neg),flush=True)
            tested+=1
    print('n',n,'flow_admissible_signed_instances',fa,'secs',round(time.monotonic()-t0,1),flush=True)
