# 334808: search connected graphs for G_SR (on boundary) complete bipartite K_{r,s}, r,s>=2
import sys,json
sys.path.insert(0,sys.argv[1]); import g6
path=sys.argv[2]; start=int(sys.argv[3]); count=int(sys.argv[4]) if sys.argv[4]!='all' else None
def layers(n,adj,v):
    L=[1<<v]; seen=1<<v; fr=1<<v
    while True:
        nx=0; x=fr
        while x:
            b=x&-x; i=b.bit_length()-1; nx|=adj[i]; x^=b
        nx&=~seen
        if not nx: return L
        L.append(nx); seen|=nx; fr=nx
hits=[]; near={}; tot=0
for k,line in g6.stream(path,start,count):
    n,adj=g6.parse(line); tot+=1
    Ls=[layers(n,adj,v) for v in range(n)]
    dist=[[0]*n for _ in range(n)]
    for v in range(n):
        for d,m in enumerate(Ls[v]):
            x=m
            while x:
                b=x&-x; dist[v][b.bit_length()-1]=d; x^=b
    # md[u] bitmask of v such that u maximally distant from v
    sr=[0]*n
    for u in range(n):
        for v in range(n):
            if u==v: continue
            d=dist[u][v]
            Lv=Ls[v]
            if d+1<len(Lv) and adj[u]&Lv[d+1]: continue
            Lu=Ls[u]
            if d+1<len(Lu) and adj[v]&Lu[d+1]: continue
            sr[u]|=1<<v
    B=[u for u in range(n) if sr[u]]
    if len(B)<4: continue
    v=B[0]; U2=sr[v]; Bm=0
    for u in B: Bm|=1<<u
    U1=Bm&~U2
    ok=True; miss=0
    for u in B:
        want = (Bm&~U2) if (U2>>u)&1 else U2
        if sr[u]!=want: ok=False; miss+=bin(sr[u]^want).count('1')
    c1=bin(U1).count('1'); c2=bin(U2).count('1')
    if ok and c1>=2 and c2>=2: hits.append((k,line.strip(),c1,c2))
    elif c1>=2 and c2>=2 and miss<=4: near.setdefault(miss,[]).append((line.strip(),c1,c2))
print(json.dumps({'file':path,'start':start,'count':tot,'hits':hits,'near_counts':{m:len(v) for m,v in near.items()},'near_examples':{m:v[:5] for m,v in near.items()}}))
