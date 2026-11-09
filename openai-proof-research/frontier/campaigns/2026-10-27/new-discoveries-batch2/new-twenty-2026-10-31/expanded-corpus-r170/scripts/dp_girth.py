# G in bad small graphs (and bad cycles) x H in {McGee, Tutte-Coxeter, random cubic girth>=g}; params d p nG
import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp import bfs_all,strong,solve,cycle
from dp_sweep_lib import load,parse
from dp_regular_lib import rand_reg
def lcf(n,pat):
    adj=[set() for _ in range(n)]
    for i in range(n):
        adj[i].add((i+1)%n); adj[(i+1)%n].add(i)
        j=(i+pat[i%len(pat)])%n; adj[i].add(j); adj[j].add(i)
    return [sorted(s) for s in adj]
d=int(sys.argv[1]);p=int(sys.argv[2]);nG=int(sys.argv[3]);lim=int(sys.argv[4])
Gs=[]
for m in range(3,40):
    D=bfs_all(cycle(m))
    if max(D[0])>=p+1 and solve(m,lambda a,b:D[a][b],d,p)[0] is None: Gs.append(('C%d'%m,D))
for n in range(2,nG+1):
    for s in load(n):
        D=bfs_all(parse(s))
        if max(max(r) for r in D)<p+1: continue
        if solve(n,lambda a,b:D[a][b],d,p)[0] is None: Gs.append((s,D))
Hs=[('McGee',lcf(24,[12,7,-7])),('TutteCoxeter',lcf(30,[-13,-9,7,-7,9,13]))]
for s in range(3):
    a=rand_reg(40,3,100+s,7)
    if a: Hs.append(('Rcub40g7s%d'%s,a))
print('Gs',[g[0] for g in Gs],flush=True)
t=time.time()
for hn,H in Hs:
    DH=bfs_all(H)
    for gn,DG in Gs:
        N,dist=strong(DG,DH)
        try: r,nodes=solve(N,dist,d,p,limit=lim)
        except TimeoutError: print(gn,hn,'TIMEOUT',flush=True); continue
        print(gn,hn,'FOUND '+str(r) if r else 'none',nodes,flush=True)
        if time.time()-t>115: print('time cap');sys.exit()
