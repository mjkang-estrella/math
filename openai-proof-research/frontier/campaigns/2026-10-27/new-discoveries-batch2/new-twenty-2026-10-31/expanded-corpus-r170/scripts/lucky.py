# Test eta(G) <= chi(G): exists vertex weighting w: V->{1..k}, k=chi(G), with sum_{N(u)} w != sum_{N(v)} w for every edge uv.
import sys,time,gzip
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp_sweep_lib import parse
def chi(adj):
    n=len(adj)
    order=sorted(range(n),key=lambda v:-len(adj[v]))
    for k in range(1,n+1):
        col=[-1]*n
        def rec(i):
            if i==n: return True
            v=order[i]; used={col[w] for w in adj[v]}
            for c in range(min(k,max(col)+2)):
                if c not in used:
                    col[v]=c
                    if rec(i+1): return True
            col[v]=-1; return False
        if rec(0): return k
def bip(adj):
    col={0:0};q=[0]
    for u in q:
        for w in adj[u]:
            if w not in col: col[w]=1-col[u];q.append(w)
            elif col[w]==col[u]: return False
    return True
def lucky(adj,k):
    n=len(adj)
    # order vertices; an edge uv is checkable once N(u) and N(v) all assigned
    order=sorted(range(n),key=lambda v:-len(adj[v])); pos={v:i for i,v in enumerate(order)}
    ready=[max(pos[x] for x in adj[v]) if adj[v] else -1 for v in range(n)]
    checks=[[] for _ in range(n)]
    for u in range(n):
        for v in adj[u]:
            if u<v: checks[max(ready[u],ready[v])].append((u,v))
    w=[0]*n
    def s(v): return sum(w[x] for x in adj[v])
    def rec(i):
        if i==n: return True
        v=order[i]
        for c in range(1,k+1):
            w[v]=c
            if all(s(a)!=s(b) for a,b in checks[i]) and rec(i+1): return True
        w[v]=0; return False
    return rec(0)
if __name__=='__main__':
    n=int(sys.argv[1]); mode=sys.argv[2]; start=int(sys.argv[3]); cnt=int(sys.argv[4])
    path=f'sources/graphdata/graph{n}c.g6'+('.gz' if n==10 else ''); op=gzip.open if n==10 else open
    t=time.time(); tested=0; bad=0; last=start
    with op(path,'rt') as f:
        for idx,line in enumerate(f):
            if idx<start: continue
            if idx>=start+cnt: break
            last=idx; adj=parse(line)
            if mode=='bip':
                if not bip(adj): continue
                k=2
            else: k=chi(adj)
            tested+=1
            if not lucky(adj,k): bad+=1; print('COUNTER',idx,line.strip(),'chi',k,flush=True)
            if time.time()-t>115: print('timecap at',idx);break
    print('n',n,mode,start,last,'tested',tested,'bad',bad,round(time.time()-t,1))
