"""Exact integer diagnostic only; no universal proof or Lean certificate."""
from itertools import combinations
import json,time
from pathlib import Path

def run(n):
 edges=list(combinations(range(n),2));m=len(edges);full=(1<<n)-1
 gam=[];bond=[];checked=0;viol=[];critical_cut=[];local_fail=[]
 def connected(adj,keep):
  if keep.bit_count()<2:return True
  seen=keep&-keep;front=seen
  while front:
   b=front&-front;front-=b;new=adj[b.bit_length()-1]&keep&~seen;seen|=new;front|=new
  return seen==keep
 for mask in range(1<<m):
  adj=[0]*n
  for j,(u,v) in enumerate(edges):
   if mask>>j&1:adj[u]|=1<<v;adj[v]|=1<<u
  def gamma(keep):
   best=keep.bit_count();s=keep
   while True:
    closed=s;z=s
    while z:
     b=z&-z;z-=b;closed|=adj[b.bit_length()-1]
    best=min(best,2*s.bit_count()+(keep&~closed).bit_count())
    if s==0:return best
    s=(s-1)&keep
  g=gamma(full);gam.append(g);bb=100
  for j in range(m):
   if mask>>j&1:
    h=mask^(1<<j);bb=min(bb,1 if gam[h]>g else 1+bond[h])
  bond.append(bb)
  if not connected(adj,full):continue
  checked+=1;deg=[a.bit_count() for a in adj];D=max(deg)
  if all(d==n-1 for d in deg):k=n-1
  else:
   k=n-1
   for size in range(1,n-1):
    if any(not connected(adj,full^sum(1<<v for v in S)) for S in combinations(range(n),size)):
     k=size;break
  bound=2*D+k-3
  if bb>bound:viol.append(dict(mask=mask,b=bb,bound=bound))
  if k==1 and all(gamma(full^(1<<v))==g-1 for v in range(n)) and len(critical_cut)<3:
   critical_cut.append(dict(mask=mask,edges=[e for j,e in enumerate(edges) if mask>>j&1],gamma=g,b=bb,Delta=D))
  local=100
  for y in range(n):
   for x,z in combinations([v for v in range(n) if adj[y]>>v&1],2):
    corr=(adj[y]&(adj[x]|adj[z])).bit_count();common=(adj[x]&adj[z]).bit_count()
    local=min(local,deg[x]+deg[y]+deg[z]-corr-3,deg[x]+deg[y]+deg[z]-corr-common-1)
  if local>bound and len(local_fail)<3:local_fail.append(dict(mask=mask,edges=[e for j,e in enumerate(edges) if mask>>j&1],gamma=g,b=bb,Delta=D,kappa=k,local_bound=local,target=bound))
 return dict(n=n,labelled_connected_checked=checked,violations=viol,critical_cut_examples=critical_cut,local_bound_insufficient=local_fail)
if __name__=='__main__':
 start=time.time();r=[run(n) for n in range(3,7)];Path('roman-diagnostics.json').write_text(json.dumps(dict(status='diagnostic only; not Lean checked',seconds=time.time()-start,results=r),indent=2));print(json.dumps(r))
