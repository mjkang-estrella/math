# Bounded sanity check for MathDB 339455 (not a proof): all labeled trees on n<=N vertices via Pruefer codes;
# for each labeled degree vector, matching numbers realized must form an integer interval.
# Also checks |nu(T)-nu(T')|<=1 for every tree-preserving 2-switch on sampled trees.
import sys,itertools,heapq,json,random
def pruefer(seq,n):
    deg=[1]*n
    for x in seq: deg[x]+=1
    leaves=[i for i in range(n) if deg[i]==1];heapq.heapify(leaves);E=[]
    for x in seq:
        l=heapq.heappop(leaves);E.append((l,x));deg[x]-=1
        if deg[x]==1: heapq.heappush(leaves,x)
    a=heapq.heappop(leaves);b=heapq.heappop(leaves);E.append((a,b));return E
def nu_tree(E,n):
    adj=[[] for _ in range(n)]
    for a,b in E: adj[a].append(b);adj[b].append(a)
    # greedy leaf matching is optimal on forests
    deg=[len(x) for x in adj];alive=[True]*n;matched=[False]*n;st=[i for i in range(n) if deg[i]<=1];c=0
    while st:
        v=st.pop()
        if not alive[v]: continue
        alive[v]=False
        nb=[u for u in adj[v] if alive[u]]
        if nb and not matched[v]:
            u=nb[0];alive[u]=False;c+=1
            for w in adj[u]:
                if alive[w]:
                    deg[w]-=1
                    if deg[w]<=1: st.append(w)
        for u in nb:
            if alive[u]:
                deg[u]-=1
                if deg[u]<=1: st.append(u)
    return c
N=int(sys.argv[1]);bad=[];stats={}
for n in range(3,N+1):
    S={}
    for seq in itertools.product(range(n),repeat=n-2):
        E=pruefer(seq,n);d=[0]*n
        for x in seq: d[x]+=1
        key=tuple(d);S.setdefault(key,set()).add(nu_tree(E,n))
    nb=0
    for k,v in S.items():
        if max(v)-min(v)+1!=len(v): bad.append((n,k,sorted(v)));nb+=1
    stats[n]=dict(degree_vectors=len(S),nonconstant=sum(1 for v in S.values() if len(v)>1),max_spread=max(max(v)-min(v) for v in S.values()),violations=nb)
    print(n,json.dumps(stats[n]),flush=True)
print('violations',bad[:5],'total',len(bad))
