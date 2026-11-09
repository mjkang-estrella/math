# For (d,p): bad connected G (order<=nG, diam>=p+1, gamma=inf) vs H in cycles C_k (k<=K) + McGee + TutteCoxeter + Q4 + tori.
import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp import bfs_all,strong,solve,cycle
from dp_sweep_lib import load,parse
from dp_regular_lib import cube,torus,gp
def lcf(n,pat):
    adj=[set() for _ in range(n)]
    for i in range(n):
        adj[i].add((i+1)%n); adj[(i+1)%n].add(i); j=(i+pat[i%len(pat)])%n; adj[i].add(j); adj[j].add(i)
    return [sorted(s) for s in adj]
d,p,nG,K,lim=map(int,sys.argv[1:6]); budget=float(sys.argv[6]) if len(sys.argv)>6 else 110
t0=time.time()
bad=[]
for m in range(3,45):
    D=bfs_all(cycle(m))
    if max(D[0])>=p+1 and solve(m,lambda a,b:D[a][b],d,p)[0] is None: bad.append(('C%d'%m,D))
for n in range(2,nG+1):
    for s in load(n):
        D=bfs_all(parse(s))
        if max(max(r) for r in D)<p+1: continue
        if solve(n,lambda a,b:D[a][b],d,p)[0] is None: bad.append((s,D))
print('d',d,'p',p,'bad',len(bad),[b[0] for b in bad][:30],round(time.time()-t0,1),flush=True)
Hs=[('C%d'%k,cycle(k)) for k in range(2*p+2,K+1)]+[('McGee',lcf(24,[12,7,-7])),('TC',lcf(30,[-13,-9,7,-7,9,13])),('Q4',cube(4)),('T6x6',torus(6,6))]
res={'found':[],'none':0,'to':0}
for gn,DG in bad:
    if gn.startswith('C') and gn[1:].isdigit(): Hc=[h for h in Hs if not (h[0].startswith('C') and h[0][1:].isdigit())]
    else: Hc=Hs
    for hn,H in Hc:
        DH=bfs_all(H); N,dist=strong(DG,DH)
        try: r,nodes=solve(N,dist,d,p,limit=lim)
        except TimeoutError: res['to']+=1; print('TO',gn,hn,flush=True); continue
        if r: res['found'].append((gn,hn,r)); print('FOUND',gn,hn,r,flush=True)
        else: res['none']+=1
        if time.time()-t0>budget: print('budget stop at',gn,hn,res);sys.exit()
print(res)
