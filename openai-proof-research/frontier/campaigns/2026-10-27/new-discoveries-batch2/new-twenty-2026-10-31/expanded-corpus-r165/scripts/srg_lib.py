def layers(n,adj,v):
    L=[1<<v]; seen=1<<v; fr=1<<v
    while True:
        nx=0; x=fr
        while x:
            b=x&-x; i=b.bit_length()-1; nx|=adj[i]; x^=b
        nx&=~seen
        if not nx: return L
        L.append(nx); seen|=nx; fr=nx
def srg(n,adj):
    Ls=[layers(n,adj,v) for v in range(n)]
    dist=[[0]*n for _ in range(n)]
    for v in range(n):
        for d,m in enumerate(Ls[v]):
            x=m
            while x:
                b=x&-x; dist[v][b.bit_length()-1]=d; x^=b
    sr=[0]*n
    for u in range(n):
        for v in range(n):
            if u==v: continue
            d=dist[u][v]
            if d+1<len(Ls[v]) and adj[u]&Ls[v][d+1]: continue
            if d+1<len(Ls[u]) and adj[v]&Ls[u][d+1]: continue
            sr[u]|=1<<v
    return sr
def from_edges(n,E):
    adj=[0]*n
    for a,b in E: adj[a]|=1<<b; adj[b]|=1<<a
    return adj
def show(n,sr): return {u:[v for v in range(n) if sr[u]>>v&1] for u in range(n) if sr[u]}
