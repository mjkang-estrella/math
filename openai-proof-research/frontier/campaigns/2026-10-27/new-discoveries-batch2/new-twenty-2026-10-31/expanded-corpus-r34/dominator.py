import resource,itertools
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
# Source operational convention, inferred from its path proofs: sinks exempt.
# This is a diagnostic convention, not a certified semantic bridge.
for m,k in [(2,3),(3,2),(2,4),(3,3)]:
 n=1+m*k;edges=[(0 if j==0 else 1+a*k+j-1,1+a*k+j) for a in range(m) for j in range(k)];adj=[0]*n
 for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
 outs=[]
 for o in range(1<<len(edges)):
  out=[0]*n
  for e,(u,v) in enumerate(edges):
   if o>>e&1:u,v=v,u
   out[u]|=1<<v
  outs.append(out)
 best=[n+1]*len(outs);cls=[0]*n;count=[0]
 def rec(v,nc):
  if v==n:
   count[0]+=1
   for i,out in enumerate(outs):
    if best[i]<=nc:continue
    if all(not o or any(c&o==c for c in cls[:nc]) for o in out):best[i]=nc
   return
  for c in range(nc+1):
   if cls[c]&adj[v]:continue
   cls[c]|=1<<v;rec(v+1,nc+(c==nc));cls[c]^=1<<v
 rec(0,0)
 print(dict(m=m,k=k,n=n,orientations=len(outs),proper_partitions=count[0],minimum=min(best),maximum=max(best),conjectured_minimum=3+m*(k//2-1),conjectured_maximum=m*(k-1)+2),flush=True)
