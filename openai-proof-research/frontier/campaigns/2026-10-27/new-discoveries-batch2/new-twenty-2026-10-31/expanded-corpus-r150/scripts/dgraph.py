# Random small-digraph probe for arXiv:1901.07509 Conjecture 2 (MathDB 341639).
# D-graph: loopless simple digraph, all in-degrees >=1, out-degree 0 or >=D, mu_int(G^T) >= ceil(K/D).
# mu_ext(G) = min |I| s.t. every non-sink outside I is reachable from I (path length>=1).
# mu_int(G^T) = min |J| s.t. every non-sink (of G) outside J reaches J in G.
import sys, random, itertools, time
seed,trials,Kmin,Kmax,D=map(int,sys.argv[1:6]); random.seed(seed)
def reach(K,adj):
    R=[]
    for s in range(K):
        seen=0; st=[s]
        while st:
            v=st.pop()
            for w in adj[v]:
                if not seen>>w&1: seen|=1<<w; st.append(w)
        R.append(seen)   # nodes reachable by path length >=1
    return R
def minset(K,ok):
    for r in range(K+1):
        for S in itertools.combinations(range(K),r):
            m=0
            for v in S: m|=1<<v
            if ok(m): return r
    return K+1
stats={}; found=0; t0=time.monotonic()
for tr in range(trials):
    K=random.randint(Kmin,Kmax); adj=[[] for _ in range(K)]
    for v in range(K):
        if random.random()<0.35: continue  # sink
        d=random.randint(D,K-1); adj[v]=random.sample([w for w in range(K) if w!=v],d)
    indeg=[0]*K
    for v in range(K):
        for w in adj[v]: indeg[w]+=1
    if min(indeg)<1: continue
    R=reach(K,adj); nons=[v for v in range(K) if adj[v]]
    # Rin[v]: nodes that reach v
    def okint(J): return all((J>>u&1) or (R[u]&J) for u in nons)
    h=minset(K,okint)
    need=-(-K//D)
    stats[K]=stats.get(K,[0,0]); stats[K][0]+=1
    if h<need: continue
    stats[K][1]+=1
    def okext(I):
        for u in nons:
            if I>>u&1: continue
            if not any((I>>v&1) and (R[v]>>u&1) for v in range(K)): return False
        return True
    mu=minset(K,okext)
    print('DGRAPH K',K,'D',D,'h',h,'mu_ext',mu,'bound',K//(D+1),'adj',adj,flush=True)
    if mu>K//(D+1): found+=1; print('COUNTEREXAMPLE',flush=True)
print('stats K:[tested,Dgraphs]',stats,'counterexamples',found,'secs',round(time.monotonic()-t0,1))
