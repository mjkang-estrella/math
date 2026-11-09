# 349834: compare D(GP(n,s)) with D(C_n(1,s)) per the printed formula.
import sys
from collections import deque
def ecc_from(adj,src,N):
    d=[-1]*N; d[src]=0; q=deque([src]); m=0
    while q:
        x=q.popleft()
        for y in adj[x]:
            if d[y]<0: d[y]=d[x]+1; m=d[y]; q.append(y)
    return m if min(d)>=0 else None
def gp(n,s):
    adj=[[] for _ in range(2*n)]
    for i in range(n):
        for (u,v) in ((i,(i+1)%n),(n+i,n+(i+s)%n),(i,n+i)):
            adj[u].append(v); adj[v].append(u)
    return adj
def circ(n,s):
    adj=[[] for _ in range(n)]
    for i in range(n):
        for t in (1,s): 
            adj[i].append((i+t)%n); adj[i].append((i-t)%n)
    return adj
N1,N2=int(sys.argv[1]),int(sys.argv[2])
bad=[]
for n in range(N1,N2+1):
    for s in range(2,(n-1)//2+1):
        A=gp(n,s); 
        # GP(n,s) automorphisms: rotations; eccentricity of outer vertex 0 and inner vertex n suffice
        dg=max(ecc_from(A,0,2*n),ecc_from(A,n,2*n))
        dc=ecc_from(circ(n,s),0,n)
        p=n//4
        pred = dc+1 if (n%4==0 and s==2*p-1 and p>2) else dc+2
        if dg!=pred: bad.append((n,s,dg,dc,pred))
print(len(bad)); print(bad[:60])
