# Cross-check completeness of hypergroup_layered.py against the McKay catalogue (n<=10): compare the sets of
# rooted-graph invariant hashes (root-individualised colour refinement + distance profile) of all pointed graphs
# satisfying (S1),(S2), per (n, r).
import sys, json, subprocess
exec(open(sys.path[0]+'/hypergroup_search.py').read().split('t=time.time(); tot=0')[0])
def inv(n,A,v0):
    D=dist_all(n,A); col=[(D[v0][v],tuple(sorted(D[v]))) for v in range(n)]
    for _ in range(n):
        new=[(col[v],tuple(sorted(col[w] for w in A[v]))) for v in range(n)]
        m={c:i for i,c in enumerate(sorted(set(new)))}; new=[m[c] for c in new]
        if len(set(new))==len(set(col)) and _>0: col=new; break
        col=new
    return (n,len(A[0]),tuple(sorted(col)),tuple(sorted(tuple(sorted(D[v])) for v in range(n))))
cat={}
for path in sys.argv[1:]:
    for line in open(path,'rb'):
        line=line.decode().strip()
        if not line: continue
        n,adj=g6(line)
        if len({len(a) for a in adj})!=1: continue
        D=dist_all(n,adj)
        for v0 in range(n):
            if check(n,adj,v0,D) is not None: cat.setdefault((n,len(adj[0])),set()).add(inv(n,adj,v0))
# generator side: re-run generator logic inline collecting invariants
gen={}
src=open(sys.path[0]+'/hypergroup_layered.py').read()
for (n,r) in sorted(cat):
    if r<2 or n<5: continue
    code=src.replace("    if not (res[0] and res[1]):","    GEN.add(inv(n,A,0))\n    if not (res[0] and res[1]):")
    g={'GEN':set(),'inv':inv,'__name__':'gen'}
    sys.argv=['x',str(n),str(r),'60']
    import io,contextlib
    with contextlib.redirect_stdout(io.StringIO()): exec(code,g)
    gen[(n,r)]=g['GEN']
    print(n,r,'catalogue classes',len(cat[(n,r)]),'generator classes',len(g['GEN']),'equal',cat[(n,r)]==g['GEN'])
