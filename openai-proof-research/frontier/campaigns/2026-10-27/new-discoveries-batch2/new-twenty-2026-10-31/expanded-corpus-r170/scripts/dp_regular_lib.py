# Test C_m strong H for structured / random regular H (d,p given). Deterministic seeds.
import sys,random,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp import bfs_all,strong,solve,cycle
def gp(n,k):
    adj=[[] for _ in range(2*n)]
    def e(a,b): adj[a].append(b); adj[b].append(a)
    for i in range(n): e(i,(i+1)%n); e(i,n+i); e(n+i,n+(i+k)%n)
    return adj
def cube(q):
    return [[v^(1<<i) for i in range(q)] for v in range(1<<q)]
def torus(a,b):
    return [[((i+di)%a)*b+(j+dj)%b for di,dj in ((1,0),(-1,0),(0,1),(0,-1))] for i in range(a) for j in range(b)]
def rand_reg(n,k,seed,girth=0,tries=2000):
    rnd=random.Random(seed)
    for _ in range(tries):
        pts=[v for v in range(n) for _ in range(k)]; rnd.shuffle(pts)
        adj=[set() for _ in range(n)]; ok=True
        for i in range(0,len(pts),2):
            a,b=pts[i],pts[i+1]
            if a==b or b in adj[a]: ok=False;break
            adj[a].add(b); adj[b].add(a)
        if not ok: continue
        adj=[sorted(s) for s in adj]
        D=bfs_all(adj)
        if any(x<0 for r in D for x in r): continue
        if girth:
            # girth via BFS: shortest cycle
            g=10**9
            for s in range(n):
                dist={s:0};par={s:-1};q=[s]
                for u in q:
                    for w in adj[u]:
                        if w not in dist: dist[w]=dist[u]+1;par[w]=u;q.append(w)
                        elif par[u]!=w: g=min(g,dist[u]+dist[w]+1)
            if g<girth: continue
        return adj
    return None
