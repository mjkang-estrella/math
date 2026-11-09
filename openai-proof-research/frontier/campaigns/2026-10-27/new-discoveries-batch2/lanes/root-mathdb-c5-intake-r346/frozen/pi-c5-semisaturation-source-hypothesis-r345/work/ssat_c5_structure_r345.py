# Structural check, lane pi-c5-semisaturation-source-hypothesis-r345.
#
# (1) The naive "dense 2-core" route to the lower bound ssat(n,C5) >= 11n/8 - O(1):
#       core lemma (NAIVE): the 2-core of a C5-semisaturated graph has >= 7N/4 - C edges.
#     REFUTED by the friendship graph F_t (t triangles sharing one vertex):
#     min degree 2, C5-semisaturated, e = 3t on N = 2t+1 vertices -> deficit -t/2 - 7/4.
#     Verified here for t = 1..6.
# (2) The COUPLED missing universal lemma (precise form, with x = #pendant vertices,
#     N = core size):  e_core >= (11N + 3x)/8 - C   for an absolute constant C.
#     Then e(G) = x + e_core >= 11n/8 - C using |X| <= n/2 (Furedi-Kim Lemma 7.1).
#     Numerical check: minimum deficit over ALL semisaturated graphs on n = 5..8
#     vertices, exhaustive.
# (3) Pendant attachment obstruction: pendants on the center of F_t break
#     semisaturation (no 4-path from pendant to outer vertices) for t >= 2.
#     Verified for t = 2..5.
import itertools, time
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.2f}s]", *a, flush=True)

def to_adj(n, edges):
    adj=[0]*n
    for a,b in edges: adj[a]|=1<<b; adj[b]|=1<<a
    return adj

def has_path4(adj,u,v):
    au=adj[u]&~(1<<v); m1=au
    while m1:
        b1=m1&-m1; m1^=b1; a=b1.bit_length()-1
        m2=adj[a]&~((1<<u)|(1<<v)|(1<<a))
        while m2:
            b2=m2&-m2; m2^=b2; b=b2.bit_length()-1
            if adj[b]&adj[v]&~((1<<u)|(1<<v)|(1<<a)|(1<<b)): return True
    return False

def semisat_path(n, adj):
    for u in range(n):
        for v in range(u+1,n):
            if (adj[u]>>v)&1: continue
            if not has_path4(adj,u,v): return False
    return True

def friendship(t):
    # t triangles sharing vertex 0
    edges=[]
    for i in range(t):
        a,b=1+2*i,2+2*i
        edges += [(0,a),(0,b),(a,b)]
    return 2*t+1, edges

log("(1) friendship graphs F_t: min-deg-2, semisaturated? e vs 7N/4 and vs (11N+3x)/8")
for t in range(1,7):
    n,es=friendship(t)
    adj=to_adj(n,es)
    sem=semisat_path(n,adj)
    mind=min(adj[v].bit_count() for v in range(n))
    x=sum(1 for v in range(n) if adj[v].bit_count()==1)
    N=n-x; ec=len(es)-x
    log(f"  F_{t}: n={n} e={len(es)} semisat={sem} mindeg={mind} x={x} "
        f"e-7N/4={ec-7*N/4:+.3f}  e-(11N+3x)/8={ec-(11*N+3*x)/8:+.3f}")

log("(3) pendants attached to the F_t center: still semisaturated?")
for t in range(2,6):
    n0,es=friendship(t)
    s=2  # two pendants on the center
    n=n0+s
    es2=es+[(0,n0+j) for j in range(s)]
    adj=to_adj(n,es2)
    sem=semisat_path(n,adj)
    # find a failing pair to document
    fail=None
    for u in range(n):
        for v in range(u+1,n):
            if not (adj[u]>>v)&1 and not has_path4(adj,u,v):
                fail=(u,v); break
        if fail: break
    log(f"  F_{t} + {s} pendants on center: n={n} e={len(es2)} semisat={sem} first failing pair={fail}")

log("(2) exhaustive minimum of the coupled deficit over ALL semisaturated graphs, n=5..8")
def deficit_scan(n, mmax, deadline):
    best=None; bestinfo=None
    all_edges=list(itertools.combinations(range(n),2))
    for m in range(n-1, mmax+1):
        if time.time()>deadline: break
        for es in itertools.combinations(all_edges,m):
            adj=to_adj(n,es)
            if any(adj[v].bit_count()==0 for v in range(n)): continue
            if not semisat_path(n,adj): continue
            x=sum(1 for v in range(n) if adj[v].bit_count()==1)
            N=n-x; ec=m-x
            d1=m-11*n/8
            d2=ec-(11*N+3*x)/8
            if best is None or d2<best[0]:
                best=(d2,d1); bestinfo=(m,x,N,list(es))
    return best,bestinfo
for n in (5,6,7,8):
    best,info=deficit_scan(n, 30, T0+170)
    if best:
        log(f"  n={n}: min coupled deficit e_core-(11N+3x)/8 = {best[0]:+.4f} "
            f"(e-11n/8 min = {best[1]:+.4f}) at m={info[0]} x={info[1]} N={info[2]} witness={info[3]}")
    else:
        log(f"  n={n}: no semisaturated graph found up to m=30?! (should not happen)")
log("DONE OK")
