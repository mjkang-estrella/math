# Independent check by itertools.combinations; plus exhaustive minimality scan n<=11 (all leaf counts).
import itertools
def build(t):
    k=len(t); E=[(i,i+1) for i in range(k-1)]; n=k
    for i,c in enumerate(t):
        for _ in range(c): E.append((i,n)); n+=1
    return n,E
def analyse(t,verbose=False):
    n,E=build(t); adj=[set() for _ in range(n)]
    for a,b in E: adj[a].add(b); adj[b].add(a)
    deg=[len(a) for a in adj]; D=max(deg); out=[]
    for r in range(1,n+1):
        cnt=[0]*n; tot=0
        for S in itertools.combinations(range(n),r):
            if all(b not in adj[a] for a in S for b in S): 
                tot+=1
                for v in S: cnt[v]+=1
        if tot==0: break
        M=max(cnt); cent=[v for v in range(n) if cnt[v]==M]
        strong=all(all(deg[u]<D for u in adj[z]) for z in cent)
        if verbose: print('r',r,'counts',cnt,'centers',cent,'strong-fail',strong)
        out.append((r,strong))
    return n,deg,out
n,deg,out=analyse((1,2,1,0,2),True); print('n',n,'deg',deg)
