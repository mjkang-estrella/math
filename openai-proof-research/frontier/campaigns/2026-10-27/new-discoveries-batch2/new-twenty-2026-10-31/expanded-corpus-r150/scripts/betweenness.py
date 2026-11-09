# Search for counterexample families to Szabo's tight-star conjecture (arXiv:1708.05075 Conj. 1):
# weighted graph = path x_0..x_{L-1} (unit weights) plus gadget vertices attached to the first few path vertices.
# For L in a window, compute co-size (#non-collinear triples) and the minimum number of pairs covering all
# triangles. Flag gadgets where co-size = k*n - c for constant k,c over the window but cover number > k.
import sys, itertools, random, time
random.seed(int(sys.argv[1])); trials=int(sys.argv[2]); G=int(sys.argv[3]); A=int(sys.argv[4]); W=int(sys.argv[5])
Ls=[int(x) for x in sys.argv[6].split(',')]
BOTH=int(sys.argv[7]) if len(sys.argv)>7 else 0
def dist(n,edges):
    INF=10**9; d=[[INF]*n for _ in range(n)]
    for i in range(n): d[i][i]=0
    for a,b,w in edges:
        if w<d[a][b]: d[a][b]=d[b][a]=w
    for k in range(n):
        dk=d[k]
        for i in range(n):
            dik=d[i][k]
            if dik>=INF: continue
            di=d[i]
            for j in range(n):
                v=dik+dk[j]
                if v<di[j]: di[j]=v
    return d
def triangles(n,d):
    T=[]
    for a,b,c in itertools.combinations(range(n),3):
        if d[a][c]==d[a][b]+d[b][c] or d[a][b]==d[a][c]+d[c][b] or d[b][c]==d[b][a]+d[a][c]: continue
        T.append((a,b,c))
    return T
def cover_number(T,kmax):
    # minimum number of pairs such that each triangle contains one; return value <= kmax+1
    if not T: return 0
    def rec(rem,k):
        if not rem: return True
        if k==0: return False
        a,b,c=rem[0]
        for p in ((a,b),(a,c),(b,c)):
            nr=[t for t in rem if not (p[0] in t and p[1] in t)]
            if rec(nr,k-1): return True
        return False
    for k in range(kmax+1):
        if rec(T,k): return k
    return kmax+1
found=0; t0=time.monotonic(); stats={}
for tr in range(trials):
    # gadget: G extra vertices; each extra vertex gets 1-3 edges to path vertices among first A, or to earlier gadget vertices
    gedges=[]
    for g in range(G):
        deg=random.randint(1,3); targets=set()
        for _ in range(deg):
            if g>0 and random.random()<0.3: targets.add(('g',random.randrange(g)))
            else:
                r=random.randrange(A); targets.add(('p',r if (BOTH==0 or random.random()<0.5) else -1-r))
        for t in targets: gedges.append((g,t,random.randint(1,W)))
    res=[]
    for L in Ls:
        n=L+G
        edges=[(i,i+1,1) for i in range(L-1)]
        for g,(kind,j),w in gedges:
            edges.append((L+g, (j if j>=0 else L+j) if kind=='p' else L+j, w))
        d=dist(n,edges)
        if any(x>=10**9 for row in d for x in row): res=None; break
        T=triangles(n,d); res.append((n,len(T),T))
    if res is None: continue
    cs=[r[1] for r in res]; ns=[r[0] for r in res]
    k=cs[1]-cs[0]
    if k>6: continue
    if k<=0 or any(cs[i+1]-cs[i]!=k for i in range(len(cs)-1)): continue
    c=k*ns[0]-cs[0]
    stats[k]=stats.get(k,0)+1
    cov=cover_number(res[-1][2],k)
    if cov>k:
        found+=1
        print('FLAG k',k,'c',c,'cover>',k,'gadget',gedges,'cosizes',cs,flush=True)
print('linear slopes',sorted(stats.items()))
print('done trials',trials,'flags',found,'secs',round(time.monotonic()-t0,1))
