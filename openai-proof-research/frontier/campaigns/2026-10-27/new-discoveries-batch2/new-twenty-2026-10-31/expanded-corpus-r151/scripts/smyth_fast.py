# Fast Hall check: network over all partitions of n=a+b into <=A+B parts (padded tuples),
# source->p (X count), p->q for unit Robin Hood transfers (INF), q->sink (Y count).
# Reachability along unit transfers within <=m parts equals dominance (Muirhead), so max flow = max injection size.
import sys,collections,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from smyth import parts_count, combine
def allparts(n,m,mx=None):
    if mx is None: mx=n
    if m==0:
        if n==0: yield ()
        return
    for k in range(min(n,mx),-1,-1):
        if k*m<n: break
        for r in allparts(n-k,m-1,k): yield (k,)+r
def unit_moves(p):
    m=len(p); out=set()
    for i in range(m):
        for j in range(m):
            if p[i]>=p[j]+2:
                q=list(p); q[i]-=1; q[j]+=1; out.add(tuple(sorted(q,reverse=True)))
    return out
def pad(p,m): return tuple(p)+(0,)*(m-len(p))
def flow_check(A,a,B,b):
    m=A+B; n=a+b
    X={pad(p,m):v for p,v in combine(parts_count(b,A),parts_count(a,B)).items()}
    Y={pad(p,m):v for p,v in combine(parts_count(a,A),parts_count(b,B)).items()}
    P=list(allparts(n,m)); idx={p:i+2 for i,p in enumerate(P)}
    N=len(P)+2; s,t=0,1
    head=[[] for _ in range(N)]; to=[];cap=[]
    def add(u,v,c):
        head[u].append(len(to)); to.append(v); cap.append(c)
        head[v].append(len(to)); to.append(u); cap.append(0)
    INF=1<<60
    for p,v in X.items(): add(s,idx[p],v)
    for q,v in Y.items(): add(idx[q],t,v)
    for p in P:
        for q in unit_moves(p): add(idx[p],idx[q],INF)
    total=0
    while True:
        lvl=[-1]*N; lvl[s]=0; dq=collections.deque([s])
        while dq:
            u=dq.popleft()
            for e in head[u]:
                if cap[e]>0 and lvl[to[e]]<0: lvl[to[e]]=lvl[u]+1; dq.append(to[e])
        if lvl[t]<0: break
        it=[0]*N
        def dfs(u,f):
            if u==t: return f
            while it[u]<len(head[u]):
                e=head[u][it[u]]; v=to[e]
                if cap[e]>0 and lvl[v]==lvl[u]+1:
                    d=dfs(v,min(f,cap[e]))
                    if d>0: cap[e]-=d; cap[e^1]+=d; return d
                it[u]+=1
            return 0
        while True:
            f=dfs(s,INF)
            if f==0: break
            total+=f
    return sum(X.values()),sum(Y.values()),total
if __name__=='__main__':
    sys.setrecursionlimit(1000000)
    t0=time.time(); tl=float(sys.argv[2])
    for part in sys.argv[1].split(','):
        A,B,g,b0,b1=map(int,part.split(':')); found=None; last=None
        for b in range(b0,b1+1):
            if time.time()-t0>tl: print('TIMEOUT',A,B,g,'at b',b,flush=True); break
            nx,ny,f=flow_check(A,b+g,B,b); last=b
            if f<nx: found=(A,b+g,B,b,nx,ny,f); break
        print('A',A,'B',B,'gap',g,'first failure',found,'last b',last,'t',round(time.time()-t0,1),flush=True)
