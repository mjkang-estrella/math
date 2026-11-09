# Independent cross-check (no window reduction, no transfer matrix): backtracking L(3,2,1)-labeling
# of the actual circulant C_n(1,t); distances by BFS in C_n. Circulants are vertex-transitive, so
# WLOG f(0)=0 (the minimum label). Usage: n t K expected(0/1). Prints one JSON line, flushed.
import sys,json
from collections import deque
n,t,K,expect=map(int,sys.argv[1:5])
S={1,n-1,t%n,(n-t)%n}
dist=[None]*n; dist[0]=0; q=deque([0])
while q:
    u=q.popleft()
    for s in S:
        v=(u+s)%n
        if dist[v] is None: dist[v]=dist[u]+1; q.append(v)
need=[max(0,4-dist[d]) for d in range(n)]; need[0]=0
# constraints against already-labelled vertices j<i (cyclic distance (i-j) mod n)
prev=[[(j,need[(i-j)%n]) for j in range(i) if need[(i-j)%n]>0] for i in range(n)]
f=[0]*n; nodes=0
def bt(i):
    global nodes
    nodes+=1
    if i==n: return True
    for x in range(K):
        if all(abs(x-f[j])>=r for j,r in prev[i]):
            f[i]=x
            if bt(i+1): return True
    return False
sys.setrecursionlimit(100000)
ok=bt(1)
print(json.dumps({'n':n,'t':t,'labels':K,'labeling_exists':ok,'expected':bool(expect),'agree':ok==bool(expect),'nodes':nodes,'witness':f if ok else None}),flush=True)
sys.exit(0 if ok==bool(expect) else 1)
