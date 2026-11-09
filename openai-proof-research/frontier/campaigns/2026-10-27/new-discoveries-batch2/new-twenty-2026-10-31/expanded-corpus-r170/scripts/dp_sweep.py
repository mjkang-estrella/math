# Sweep: G bad (gamma_d^p(G)=inf, connected, order<=nG), H connected order<=nH without (d,p)-close vertex; test G strong H.
import sys,json,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp import bfs_all,strong,solve
def parse(s):
    s=s.strip(); n=ord(s[0])-63; bits=[]
    for ch in s[1:]:
        v=ord(ch)-63
        for k in range(5,-1,-1): bits.append((v>>k)&1)
    adj=[[] for _ in range(n)]; idx=0
    for j in range(1,n):
        for i in range(j):
            if bits[idx]: adj[i].append(j); adj[j].append(i)
            idx+=1
    return adj
def load(n):
    return [l.strip() for l in open(f'sources/graphdata/graph{n}c.g6') if l.strip()]
d=int(sys.argv[1]); p=int(sys.argv[2]); nG=int(sys.argv[3]); nH=int(sys.argv[4])
def single(D):
    N=len(D); return N,(lambda a,b:D[a][b])
bad=[];noclose=[]
for n in range(2,max(nG,nH)+1):
    for s in load(n):
        adj=parse(s); D=bfs_all(adj); diam=max(max(r) for r in D)
        if diam<p+1: continue
        if n<=nG:
            N,dist=single(D); r,_=solve(N,dist,d,p)
            if r is None: bad.append((s,D))
        if n<=nH:
            close=False
            for u in range(n):
                ball=[x for x in range(n) if D[u][x]<=d]
                if all(D[x][y]<=p for x in ball for y in ball): close=True;break
            if not close: noclose.append((s,D))
print('bad',len(bad),'noclose',len(noclose),flush=True)
t=time.time();found=[];cnt=0;to=0
for gs,DG in bad:
    for hs,DH in noclose:
        N,dist=strong(DG,DH); cnt+=1
        try: r,nodes=solve(N,dist,d,p,limit=200000)
        except TimeoutError: to+=1; continue
        if r is not None:
            found.append((gs,hs,r)); print('FOUND',gs,hs,r,flush=True)
print('pairs',cnt,'timeouts',to,'found',len(found),'secs',round(time.time()-t,1))
