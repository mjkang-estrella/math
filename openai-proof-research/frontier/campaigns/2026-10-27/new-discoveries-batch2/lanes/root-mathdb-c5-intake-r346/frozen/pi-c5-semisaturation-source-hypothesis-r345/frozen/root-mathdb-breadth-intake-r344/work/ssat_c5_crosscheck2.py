# Fixed cross-validation. Count-def now normalizes edge order. Exhaustive n=6 m=7 under BOTH defs.
import itertools, time

def c5_count(n, es):
    es={tuple(sorted(e)) for e in es}; cnt=0
    for p in itertools.permutations(range(n),5):
        a,b,c,d,e = p
        if a!=min(p): continue
        E={tuple(sorted(x)) for x in ((a,b),(b,c),(c,d),(d,e),(e,a))}
        if E <= es: cnt+=1
    return cnt

def semisat_count(n, es):
    base=c5_count(n,es)
    for e in set(itertools.combinations(range(n),2))-set(tuple(sorted(x)) for x in es):
        if c5_count(n, set(map(tuple,map(sorted,es)))|{e}) <= base: return False
    return True

def semisat_path(n, es):
    adj=[0]*n
    for a,b in es: adj[a]|=1<<b; adj[b]|=1<<a
    for u in range(n):
        for v in range(u+1,n):
            if (adj[u]>>v)&1: continue
            ok=False
            for x in range(n):
                if x in (u,v) or not (adj[u]>>x)&1: continue
                for y in range(n):
                    if y in (u,v,x) or not (adj[x]>>y)&1: continue
                    for z in range(n):
                        if z in (u,v,x,y): continue
                        if (adj[y]>>z)&1 and (adj[z]>>v)&1: ok=True;break
                    if ok:break
                if ok:break
            if not ok: return False
    return True

bad=0; checked=0
for n in [5,6]:
    edges=list(itertools.combinations(range(n),2))
    for m in range(0,9):
        for es in itertools.combinations(edges,m):
            checked+=1
            if semisat_count(n,es)!=semisat_path(n,es):
                bad+=1
                if bad<4: print("MISMATCH",n,es, semisat_count(n,es), semisat_path(n,es))
print(f"agreement check: {checked} graphs, mismatches={bad}")

t0=time.time()
es6=list(itertools.combinations(range(6),2))
hits=[es for es in itertools.combinations(es6,7) if semisat_count(6,es)]
print("n=6 m=7 semisat (count-def):",len(hits),hits[:1], f"({time.time()-t0:.0f}s)")
w6=[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,4)]
print("n=6 witness m=8: count-def:",semisat_count(6,w6), "path-def:",semisat_path(6,w6))
