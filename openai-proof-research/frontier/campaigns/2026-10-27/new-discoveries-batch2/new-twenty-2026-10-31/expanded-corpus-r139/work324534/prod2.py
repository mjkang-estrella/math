# 324534 (Skowronek-Kaziow Conjecture 4.3): chi^t_Pi(G) <= 2, i.e. a total weighting with {1,2}
# whose vertex products (own weight times incident edge weights) properly colour G.
# Product of {1,2} weights = 2^(number of 2s), so equivalently a {0,1} total weighting with proper sums.
import sys, json
sys.setrecursionlimit(10000)
def solve(adj):
    n=len(adj); E=[(u,v) for v in range(n) for u in range(v) if adj[u]>>v&1]
    # order: items grouped so vertex v completes after its last incident item
    items=[]  # ('v',v) or ('e',(u,v))
    for v in range(n):
        items.append(('v',v))
        for u in range(v):
            if adj[u]>>v&1: items.append(('e',(u,v)))
    # completion time of each vertex: index of last item touching it
    last=[0]*n
    for i,(t,x) in enumerate(items):
        if t=='v': last[x]=max(last[x],i)
        else: last[x[0]]=max(last[x[0]],i); last[x[1]]=max(last[x[1]],i)
    done_at={}
    for v in range(n): done_at.setdefault(last[v],[]).append(v)
    s=[0]*n; complete=[False]*n
    def rec(i):
        if i==len(items): return True
        t,x=items[i]
        for w in (0,1):
            if t=='v': s[x]+=w
            else: s[x[0]]+=w; s[x[1]]+=w
            ok=True
            for v in done_at.get(i,[]):
                complete[v]=True
                m=adj[v]
                for u in range(n):
                    if m>>u&1 and complete[u] and u!=v and s[u]==s[v]: ok=False
            if ok and rec(i+1): return True
            for v in done_at.get(i,[]): complete[v]=False
            if t=='v': s[x]-=w
            else: s[x[0]]-=w; s[x[1]]-=w
        return False
    return rec(0)
if __name__=='__main__':
    lo,hi=int(sys.argv[1]),int(sys.argv[2]); fails=[]; tot=0
    for n in range(lo,hi+1):
        c=0
        for l in open(f'graphs/g{n}.txt'):
            if not l.strip(): continue
            g=list(map(int,l.split())); c+=1
            if not solve(g): fails.append((n,g))
        tot+=c; print(n,c,'fails so far',len(fails),flush=True)
    print(json.dumps({'graphs_checked':tot,'fails':fails[:10]}))
