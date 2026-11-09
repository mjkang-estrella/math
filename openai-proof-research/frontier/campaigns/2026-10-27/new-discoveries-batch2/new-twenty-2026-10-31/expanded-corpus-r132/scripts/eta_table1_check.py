# Check the source's Table 1 n=7 maximal pair: X values and diameters.
import sys,json
sys.path.insert(0,__file__.rsplit('/',1)[0])
from eta_local import X,diam
E=[(1,2),(2,3),(3,4),(4,5),(5,1),(2,6),(6,5),(7,6),(6,1),(3,7),(7,4)]  # G of Table 1, n=7
n=7; adj=[0]*n
for a,b in E: a-=1;b-=1; adj[a]|=1<<b; adj[b]|=1<<a
full=(1<<n)-1; cadj=[(full^adj[v])&~(1<<v) for v in range(n)]
eta=lambda A: sum(1 for S in range(1,1<<n) if __import__('eta_local').conn(S,A))
print(json.dumps({'edges_G':len(E),'X':X(adj,n),'eta_G':eta(adj),'eta_coG':eta(cadj),'sum':eta(adj)+eta(cadj),'2^n+n-1+X':2**n+n-1+X(adj,n),'diam_G':diam(adj,n),'diam_coG':diam(cadj,n)}))
