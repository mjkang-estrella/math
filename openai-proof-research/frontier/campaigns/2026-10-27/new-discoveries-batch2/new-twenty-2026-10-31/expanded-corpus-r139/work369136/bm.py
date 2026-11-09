# 369136: check gamma_b(G) <= 2 mp(G) on connected graphs. gamma_b by exact set-cover DP over
# balls N_r[v] (cost r, 1<=r<=ecc(v)); mp by brute force over vertex subsets.
import sys, json, itertools, pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'scripts'))
from graphgen import connected
def dist(adj):
    n=len(adj); D=[[None]*n for _ in range(n)]
    for s in range(n):
        D[s][s]=0; fr=[s]; d=0
        while fr:
            d+=1; nf=[]
            for v in fr:
                for w in range(n):
                    if adj[v]>>w&1 and D[s][w] is None: D[s][w]=d; nf.append(w)
            fr=nf
    return D
def gamma_b(adj,D):
    n=len(adj); full=(1<<n)-1; balls={}
    for v in range(n):
        e=max(D[v])
        for r in range(1,e+1):
            m=sum(1<<w for w in range(n) if D[v][w]<=r)
            if m not in balls or balls[m]>r: balls[m]=r
    INF=10**9; dp=[INF]*(1<<n); dp[0]=0
    bl=list(balls.items())
    for mask in range(1<<n):
        if dp[mask]==INF: continue
        # cover lowest uncovered vertex
        if mask==full: continue
        low=(~mask)&(mask+1); 
        for m,c in bl:
            if m&low:
                nm=mask|m
                if dp[mask]+c<dp[nm]: dp[nm]=dp[mask]+c
    return dp[full]
def mp(adj,D):
    n=len(adj); best=1
    balls=[[sum(1<<w for w in range(n) if D[v][w]<=k) for k in range(1,n)] for v in range(n)]
    for size in range(2,n+1):
        found=False
        for M in itertools.combinations(range(n),size):
            mm=sum(1<<v for v in M)
            if all(bin(balls[v][k-1]&mm).count('1')<=k for v in range(n) for k in range(1,n)):
                found=True; break
        if found: best=size
        else: break   # multipacking is hereditary (subsets of multipackings are multipackings)
    return best
if __name__=='__main__':
    lo,hi=int(sys.argv[1]),int(sys.argv[2]); viol=[]; tight=0; tot=0
    for n in range(lo,hi+1):
        for l in open(f'graphs/g{n}.txt'):
            if not l.strip(): continue
            g=list(map(int,l.split()))
            if not connected(g): continue
            tot+=1; D=dist(g); gb=gamma_b(g,D); m=mp(g,D)
            if gb>2*m: viol.append((n,g,gb,m))
            if gb==2*m: tight+=1
        print(n,'checked',tot,'violations',len(viol),'tight',tight,flush=True)
    print(json.dumps({'connected_graphs':tot,'violations':viol[:10],'equality_cases':tight}))
