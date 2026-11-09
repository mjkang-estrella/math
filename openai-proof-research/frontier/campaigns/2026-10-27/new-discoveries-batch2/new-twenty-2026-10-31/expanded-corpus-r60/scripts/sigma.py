from itertools import combinations
from fractions import Fraction
for n in range(1,8):
 es=list(combinations(range(n),2)); adj=[0]*n;deg=[0]*n;counts=[0,0,0];best=[-1];slack=[10**9]
 B=max([a*(n-a)*(n-2*a)**2 for a in range(1,n)]+[0])
 def visit(k,m):
  if k<len(es):
   u,v=es[k];visit(k+1,m)
   if not adj[u]&adj[v]:
    adj[u]^=1<<v;adj[v]^=1<<u;deg[u]+=1;deg[v]+=1;visit(k+1,m+1);deg[u]-=1;deg[v]-=1;adj[u]^=1<<v;adj[v]^=1<<u
   return
  counts[0]+=1;r=1
  for _ in range(n):
   for v in range(n):
    if r>>v&1:r|=adj[v]
  if r!=(1<<n)-1:return
  counts[1]+=1;M=sum(d*d for d in deg);D=n*m-M;s=n*M-4*m*m;best[0]=max(best[0],s)
  if D:counts[2]+=1;slack[0]=min(slack[0],D-n+2);assert D>=n-2,(n,adj,D)
  assert s<=B,(n,adj,s,B)
 visit(0,0)
 print(dict(n=n,trianglefree=counts[0],connected=counts[1],noncb=counts[2],min_gap_slack=slack[0] if counts[2] else None,max_sigma=best[0],B=B),flush=True)
for n in range(7,10001):
 a=1
 while 8*a*(n-a)<n*n:a+=1
 d=min(8*a*(n-a)-n*n,n*n-8*(a-1)*(n-a+1))
 assert d*d<=16*(n-3)**2
print('Integer bracketing verified n=7..10000; diagnostic only.')
for mask in range(16):
 E={(0,1),(1,2),(2,3)}|{(i,4) for i in range(4) if mask>>i&1}
 if any(all(e in E for e in combinations(t,2)) for t in combinations(range(5),3)):continue
 c=sum(sum(e in E for e in combinations((a,b,4),2))==1 for a,b in combinations(range(4),2));assert c>=1
 print('P4 extension neighbor mask',mask,'new one-edge triples',c)
