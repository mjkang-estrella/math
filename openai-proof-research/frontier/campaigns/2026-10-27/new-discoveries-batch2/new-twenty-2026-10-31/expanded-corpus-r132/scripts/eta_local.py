# eta(G)+eta(co-G) = 2^n + n - 1 + X(G), X = #{S: G[S] and co-G[S] both connected}. Hill-climb to maximise X.
import sys,random,json
def conn(mask,adj):
    # is induced subgraph on mask connected
    start=mask&-mask; seen=start; frontier=start
    while frontier:
        v=(frontier&-frontier).bit_length()-1; frontier&=frontier-1
        nb=adj[v]&mask&~seen; seen|=nb; frontier|=nb
    return seen==mask
def X(adj,n):
    full=(1<<n)-1; cadj=[(full^adj[v])&~(1<<v) for v in range(n)]
    c=0
    for S in range(1,1<<n):
        if bin(S).count('1')>=4 and conn(S,adj) and conn(S,cadj): c+=1
    return c
def diam(adj,n):
    D=0
    for s in range(n):
        dist={s:0}; fr=[s]
        while fr:
            nf=[]
            for v in fr:
                for u in range(n):
                    if adj[v]>>u&1 and u not in dist: dist[u]=dist[v]+1; nf.append(u)
            fr=nf
        if len(dist)<n: return 99
        D=max(D,max(dist.values()))
    return D
def _main():
    n=int(sys.argv[1]); reps=int(sys.argv[2]); seed=int(sys.argv[3]); rnd=random.Random(seed)
    best=-1; res=[]
    for r in range(reps):
        adj=[0]*n
        for i in range(n):
            for j in range(i+1,n):
                if rnd.random()<.5: adj[i]|=1<<j; adj[j]|=1<<i
        cur=X(adj,n); improved=True
        while improved:
            improved=False
            pairs=[(i,j) for i in range(n) for j in range(i+1,n)]; rnd.shuffle(pairs)
            for i,j in pairs:
                adj[i]^=1<<j; adj[j]^=1<<i
                v=X(adj,n)
                if v>cur: cur=v; improved=True
                else: adj[i]^=1<<j; adj[j]^=1<<i
        full=(1<<n)-1; cadj=[(full^adj[v])&~(1<<v) for v in range(n)]
        res.append((cur,diam(adj,n),diam(cadj,n),sum(bin(a).count('1') for a in adj)//2))
        best=max(best,cur)
    res.sort(reverse=True)
    print(json.dumps({'n':n,'best':best,'top':res[:12]}))
if __name__=="__main__": _main()
