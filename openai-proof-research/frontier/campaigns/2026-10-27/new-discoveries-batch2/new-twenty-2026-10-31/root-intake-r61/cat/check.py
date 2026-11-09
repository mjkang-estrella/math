import itertools,sys
def build(leafs):
    k=len(leafs);adj={i:set() for i in range(k)}
    for i in range(k-1): adj[i].add(i+1);adj[i+1].add(i)
    nxt=k
    for i,c in enumerate(leafs):
        for _ in range(c): adj[nxt]={i};adj[i].add(nxt);nxt+=1
    return adj
def indep_count_with(adj,r):
    # count independent r-sets containing each vertex via DP over tree? use simple recursion with memo on vertex order
    V=sorted(adj);n=len(V);cnt=[0]*n
    # brute force by backtracking
    def bt(start,chosen,banned,size):
        if size==r:
            for v in chosen: cnt[v]+=1
            return
        for v in range(start,n):
            if v in banned: continue
            bt(v+1,chosen+[v],banned|adj[v]|{v},size+1)
    bt(0,[],set(),0);return cnt
def min_maximal_indep(adj):
    V=sorted(adj);best=None
    # tree: brute force over small sizes via ILP-free search
    for s in range(1,len(V)+1):
        for S in itertools.combinations(V,s):
            Sset=set(S)
            if any(adj[a]&Sset for a in S): continue
            if all(v in Sset or adj[v]&Sset for v in V): return s
for leafs,r in [((1,2,1,0,2),6)]+[((m-1,m,m-1,0,m),5) for m in range(3,9)]:
    adj=build(leafs);cnt=indep_count_with(adj,r);mx=max(cnt);cent=[v for v in adj if cnt[v]==mx]
    deg={v:len(adj[v]) for v in adj};D=max(deg.values())
    nb={v:[deg[w] for w in adj[v]] for v in cent}
    mu=min_maximal_indep(adj) if len(adj)<=24 else 'skip'
    print(leafs,'n',len(adj),'r',r,'maxcent',cent,'nbrdeg',nb,'Delta',D,'mu',mu,flush=True)
