# Non-bipartite generalized Petersen graphs G(n,k), 1<=k<n/2, that are NOT cores, via a direct check of
# Theorem 2.1(b) of arXiv 2202.06785: G is a core iff some minimum odd cycle uses a spoke.
# Odd girth and "min odd cycle through a spoke" computed by BFS on the bipartite double cover.
import sys, json
from collections import deque
def gp(n,k):
    adj=[[] for _ in range(2*n)]
    for i in range(n):
        for a,b,s in ((i,(i+1)%n,0),(i,n+i,1),(n+i,n+(i+k)%n,0)):
            adj[a].append((b,s)); adj[b].append((a,s))
    return adj
def odd_girth_info(n,k):
    adj=gp(n,k); N=2*n; best=None; spoke_best=None
    # shortest odd closed walk through edge e containing a spoke: for each edge (a,b) compute shortest even-length... use
    # shortest odd cycle length through vertex: BFS on double cover tracking whether a spoke was used.
    for s in range(N):
        dist={(s,0,0):0}; q=deque([(s,0,0)])
        while q:
            v,p,sp=q.popleft(); dd=dist[(v,p,sp)]
            for w,isspoke in adj[v]:
                st=(w,p^1,sp|isspoke)
                if st not in dist: dist[st]=dd+1; q.append(st)
        for sp in (0,1):
            if (s,1,sp) in dist:
                L=dist[(s,1,sp)]
                if best is None or L<best: best=L
                if sp and (spoke_best is None or L<spoke_best): spoke_best=L
    return best, spoke_best
out=[]
for n in range(5,int(sys.argv[1])+1):
    for k in range(1,(n+1)//2):
        if 2*k==n: continue
        if n%2==0 and k%2==1: continue
        g,gs=odd_girth_info(n,k)
        # shortest odd closed walk using a spoke has length >= shortest odd cycle using a spoke; equality of
        # minima is what matters: a closed odd walk of length g (odd girth) is a cycle.
        core = (gs==g)
        if not core: out.append((n,k,g,gs))
print(json.dumps(out))
