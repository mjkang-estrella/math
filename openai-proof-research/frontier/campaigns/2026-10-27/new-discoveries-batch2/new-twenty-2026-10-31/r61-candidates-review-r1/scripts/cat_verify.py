# Independent exact verification for MathDB 366834 (reviewer r61-candidates-review-r1).
# Two independent methods: (a) brute-force enumeration of independent r-sets, (b) independence-polynomial
# DP along the spine. mu (min maximal independent set = independent domination number) by (a) brute
# force for n<=24 and (b) exact spine DP. Readings checked:
#   U  universal: every max r-centre is a leaf whose unique neighbour has degree Delta
#   E  existential: some max r-centre is a leaf whose unique neighbour has degree Delta
import itertools,sys,json
def build(leafs):
    k=len(leafs);adj={i:set() for i in range(k)}
    for i in range(k-1): adj[i].add(i+1);adj[i+1].add(i)
    nxt=k
    for i,c in enumerate(leafs):
        for _ in range(c): adj[nxt]={i};adj[i].add(nxt);nxt+=1
    return adj
def stars_brute(adj,r):
    n=len(adj);cnt=[0]*n
    def bt(start,chosen,banned):
        if len(chosen)==r:
            for v in chosen: cnt[v]+=1
            return
        for v in range(start,n):
            if v in banned: continue
            bt(v+1,chosen+[v],banned|adj[v])
    bt(0,[],set());return cnt
def padd(a,b):
    m=max(len(a),len(b));return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(m)]
def pmul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c
def indpoly_forest(adj,removed):
    # independence polynomial of forest adj minus removed, via rooted tree DP
    seen=set(removed);res=[1]
    for root in adj:
        if root in seen: continue
        # iterative DFS
        order=[];par={root:None};st=[root];seen.add(root)
        while st:
            u=st.pop();order.append(u)
            for w in adj[u]:
                if w not in seen: seen.add(w);par[w]=u;st.append(w)
        inn={};out={}
        for u in reversed(order):
            a=[0,1];b=[1]
            for w in adj[u]:
                if par.get(w)==u and w not in removed:
                    a=pmul(a,out[w]);b=pmul(b,padd(inn[w],out[w]))
            inn[u]=a;out[u]=b
        res=pmul(res,padd(inn[root],out[root]))
    return res
def stars_dp(adj,r):
    out=[]
    for v in adj:
        p=indpoly_forest(adj,set(adj[v])|{v})
        out.append(p[r-1] if r-1<len(p) else 0)
    return out
def mu_brute(adj):
    V=sorted(adj)
    for s in range(1,len(V)+1):
        for S in itertools.combinations(V,s):
            Ss=set(S)
            if any(adj[a]&Ss for a in S): continue
            if all(v in Ss or adj[v]&Ss for v in V): return s
def mu_dp(adj):
    # tree DP for independent domination: states in S / out&dominated / out&not-yet-dominated
    INF=10**9;root=0;order=[];par={root:None};st=[root]
    while st:
        u=st.pop();order.append(u)
        for w in adj[u]:
            if w!=par[u]: par[w]=u;st.append(w)
    A={};B={};C={}
    for u in reversed(order):
        ch=[w for w in adj[u] if par.get(w)==u]
        a=1+sum(min(B[w],C[w]) for w in ch)             # u in S: children out (C allowed: dominated by u)
        base=sum(min(A[w],B[w]) for w in ch)            # u out, children not C
        # B: u out and dominated by some child in S
        if ch:
            b=min(sum(min(A[x],B[x]) for x in ch if x!=w)+A[w] for w in ch)
        else: b=INF
        c=sum(B[w] for w in ch)                         # u out, not dominated by children; children must be B
        A[u]=a;B[u]=min(b,INF);C[u]=min(c,INF)
    return min(A[root],B[root])
def alpha(adj): 
    p=indpoly_forest(adj,set());return len(p)-1
def analyse(leafs,r,brute=True,mubrute=True):
    adj=build(leafs);n=len(adj);deg={v:len(adj[v]) for v in adj};D=max(deg.values())
    sd=stars_dp(adj,r)
    sb=stars_brute(adj,r) if brute else None
    if brute: assert sb==sd,(leafs,r)
    mx=max(sd);cent=[v for v in adj if sd[v]==mx]
    ok_leaf=[v for v in cent if deg[v]==1 and deg[next(iter(adj[v]))]==D]
    U=all(deg[v]==1 and deg[next(iter(adj[v]))]==D for v in cent)
    E=bool(ok_leaf)
    md=mu_dp(adj);mb=mu_brute(adj) if mubrute else None
    if mubrute: assert md==mb,(leafs,md,mb)
    return dict(leafs=leafs,n=n,r=r,alpha=alpha(adj),mu=md,mu_brute=mb,Delta=D,stars=sd,brute_agrees=brute,max_star=mx,max_centres=cent,
                centre_nbr_degrees={v:[deg[w] for w in adj[v]] for v in cent},universal_holds=U,existential_holds=E,r_le_mu_half=2*r<=md)
if __name__=='__main__':
    res=[]
    W=(1,2,1,0,2)
    for r in range(1,8): res.append(analyse(W,r))
    for m in range(3,11):
        res.append(analyse((m-1,m,m-1,0,m),5,brute=True,mubrute=(5+4*m-2)<=20))
    for x in res: print(json.dumps(x),flush=True)
