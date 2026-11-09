# Exact existence/search of a d-distance dominating p-packing in a finite graph (bitset backtracking).
import sys
from collections import deque
def bfs_all(adj):
    n=len(adj); D=[]
    for s in range(n):
        dist=[-1]*n; dist[s]=0; q=deque([s])
        while q:
            u=q.popleft()
            for w in adj[u]:
                if dist[w]<0: dist[w]=dist[u]+1; q.append(w)
        D.append(dist)
    return D
def strong(DG,DH):
    m=len(DG); n=len(DH)
    def dist(a,b):
        g1,h1=divmod(a,n); g2,h2=divmod(b,n)
        x=DG[g1][g2]; y=DH[h1][h2]
        if x<0 or y<0: return -1
        return max(x,y)
    return m*n,dist
def balls(N,dist,r):
    B=[]
    for v in range(N):
        b=0
        for w in range(N):
            x=dist(v,w)
            if 0<=x<=r: b|=1<<w
        B.append(b)
    return B
def solve(N,dist,d,p,first_fixed=None,limit=10**7):
    BD=balls(N,dist,d); BP=balls(N,dist,p); full=(1<<N)-1
    nodes=[0]
    def rec(cov,blk,S):
        nodes[0]+=1
        if nodes[0]>limit: raise TimeoutError
        if cov==full: return S
        unc=full&~cov; best=None;bc=None;bn=10**9
        x=unc
        while x:
            lb=x&-x; v=lb.bit_length()-1; x^=lb
            c=BD[v]&~blk; k=bin(c).count('1')
            if k==0: return None
            if k<bn: bn=k;best=v;bc=c
            if k==1: break
        c=bc
        while c:
            lb=c&-c; u=lb.bit_length()-1; c^=lb
            r=rec(cov|BD[u],blk|BP[u],S+[u])
            if r is not None: return r
        return None
    if first_fixed is not None:
        # vertex-transitive shortcut: some S member may be assumed equal to first_fixed? only valid if transitive; caller decides
        return rec(BD[first_fixed],BP[first_fixed],[first_fixed]),nodes[0]
    return rec(0,0,[]),nodes[0]
def cycle(n): return [[(i-1)%n,(i+1)%n] for i in range(n)]
def path(n): return [[j for j in (i-1,i+1) if 0<=j<n] for i in range(n)]
if __name__=='__main__':
    for (d,p,m,n) in [(2,3,11,8),(2,3,11,11),(2,3,6,13),(2,3,8,9),(2,3,4,4)]:
        N,dist=strong(bfs_all(cycle(m)),bfs_all(cycle(n)))
        print(d,p,'C%d x C%d'%(m,n),solve(N,dist,d,p))
    N,dist=strong(bfs_all(path(7)),bfs_all(path(9)))
    print('P7xP9 d2p3',solve(N,dist,2,3))
