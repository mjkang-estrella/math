# Exhaustive: all graphs on n<=N vertices (as extensions of non-isomorphic (n-1)-vertex graphs), compute IR-graph,
# report any IR-graph that is a path P_m (m>=3) or cycle C_m (m>=5); also tally connected IR-trees.
import sys,itertools,json,time
from collections import Counter
def canon(n,adj):
    # color refinement then brute force within cells
    col=[0]*n
    while True:
        sig=[(col[v],tuple(sorted(col[u] for u in range(n) if adj[v]>>u&1))) for v in range(n)]
        keys=sorted(set(sig)); new=[keys.index(s) for s in sig]
        if len(set(new))==len(set(col)) : col=new; break
        col=new
    cells=[[v for v in range(n) if col[v]==c] for c in sorted(set(col))]
    best=None
    for prod in itertools.product(*[itertools.permutations(c) for c in cells]):
        order=[v for p in prod for v in p]
        pos={v:i for i,v in enumerate(order)}
        code=0
        for i,v in enumerate(order):
            for j in range(i+1,n):
                if adj[v]>>order[j]&1: code|=1<<(i*n+j)
        if best is None or code<best: best=code
    return best
def graphs(N):
    lvl={0:[0]}  # n=1
    out={1:[[0]]}
    cur=[[0]]
    for n in range(2,N+1):
        seen={}
        for g in cur:
            for nb in range(1<<(n-1)):
                adj=g[:]+[nb]
                for u in range(n-1):
                    if nb>>u&1: adj[u]|=1<<(n-1)
                c=canon(n,adj)
                if c not in seen: seen[c]=adj
        cur=list(seen.values()); out[n]=cur
    return out
def connected(n,adj):
    seen=1;frontier=1
    while frontier:
        nf=0;x=frontier
        while x:
            b=x&-x;nf|=adj[b.bit_length()-1];x^=b
        frontier=nf&~seen; seen|=nf
    return seen==(1<<n)-1
def irgraph(n,adj):
    N=[adj[v]|(1<<v) for v in range(n)]
    best=0;sets=[]
    for D in range(1,1<<n):
        k=bin(D).count('1')
        if k<best: continue
        ok=True;x=D
        while x:
            b=x&-x;v=b.bit_length()-1
            others=0;y=D^b
            while y:
                c=y&-y;others|=N[c.bit_length()-1];y^=c
            if not N[v]&~others: ok=False;break
            x^=b
        if ok:
            if k>best: best=k;sets=[D]
            else: sets.append(D)
    idx={s:i for i,s in enumerate(sets)}; m=len(sets); E=set()
    for i,A in enumerate(sets):
        for j in range(i+1,m):
            B=sets[j]; d=A^B
            if bin(d).count('1')==2:
                a=(A&d).bit_length()-1; b=(B&d).bit_length()-1
                if adj[a]>>b&1: E.add((i,j))
    return best,m,E
def shape(m,E):
    deg=Counter()
    for i,j in E: deg[i]+=1;deg[j]+=1
    if m<2: return 'K1'
    # connectivity
    nb={i:[] for i in range(m)}
    for i,j in E: nb[i].append(j);nb[j].append(i)
    seen={0};st=[0]
    while st:
        v=st.pop()
        for u in nb[v]:
            if u not in seen: seen.add(u);st.append(u)
    if len(seen)<m: return 'disconnected'
    if len(E)==m-1:
        if max(deg.values())<=2: return 'path%d'%m
        return 'tree%d'%m
    if len(E)==m and all(deg[i]==2 for i in range(m)): return 'cycle%d'%m
    return 'other'
if __name__=='__main__':
    N=int(sys.argv[1]); t0=time.time()
    gs=graphs(N-1)
    print('nonisomorphic counts',{k:len(v) for k,v in gs.items()},round(time.time()-t0,1),flush=True)
    tally=Counter(); hits=[]
    # all graphs on <=N-1 vertices directly, and all extensions to N vertices
    for n in range(1,N):
        for adj in gs[n]:
            if not connected(n,adj): continue
            b,m,E=irgraph(n,adj); s=shape(m,E); tally[(n,s if not s.startswith('tree') else 'tree')]+=1
            if s.startswith('path') and m>=3 or s.startswith('cycle') and m>=5 or s.startswith('tree'): hits.append((n,adj,s,b))
    n=N
    for g in gs[N-1]:
        for nb in range(1<<(N-1)):
            adj=g[:]+[nb]
            for u in range(N-1):
                if nb>>u&1: adj[u]|=1<<(N-1)
            if not connected(N,adj): continue
            b,m,E=irgraph(N,adj); s=shape(m,E); tally[(N,s if not s.startswith('tree') else 'tree')]+=1
            if s.startswith('path') and m>=3 or s.startswith('cycle') and m>=5 or s.startswith('tree'): hits.append((N,adj,s,b))
    print(json.dumps({'N':N,'secs':round(time.time()-t0,1),'tally':{f'{k[0]}:{k[1]}':v for k,v in sorted(tally.items())},'path_cycle_hits':[h for h in hits if not h[2].startswith('tree')],'tree_hits_sample':[h for h in hits if h[2].startswith('tree')][:20],'n_tree_hits':sum(1 for h in hits if h[2].startswith('tree'))}))
