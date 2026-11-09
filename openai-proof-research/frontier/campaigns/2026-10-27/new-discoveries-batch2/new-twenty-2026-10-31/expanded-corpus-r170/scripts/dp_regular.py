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
d=int(sys.argv[1]);p=int(sys.argv[2]);m=int(sys.argv[3]);which=sys.argv[4]
Hs=[]
if which=='struct':
    Hs+= [('Q4',cube(4)),('Q5',cube(5))]
    Hs+= [('T%dx%d'%(a,b),torus(a,b)) for a in range(5,10) for b in range(a,10)]
    Hs+= [('GP(%d,%d)'%(n,k),gp(n,k)) for n in range(5,17) for k in range(1,n//2+1) if 2*k!=n]
else:
    n=int(which.split(':')[1]); k=int(which.split(':')[2]); gi=int(which.split(':')[3]); cnt=int(which.split(':')[4])
    for s in range(cnt):
        a=rand_reg(n,k,s,gi)
        if a: Hs.append(('R%d_%d_s%d'%(n,k,s),a))
DG=bfs_all(cycle(m))
t=time.time()
for name,H in Hs:
    DH=bfs_all(H)
    N,dist=strong(DG,DH)
    try: r,nodes=solve(N,dist,d,p,limit=300000)
    except TimeoutError: print(name,'TIMEOUT',flush=True); continue
    print(name,len(H),'FOUND' if r else 'none',nodes,r if r else '',flush=True)
    if time.time()-t>110: print('time cap');break
