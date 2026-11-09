import json,time
from pathlib import Path
start=time.monotonic();out=[]
def clique(adj):
 best=0
 def go(P,s):
  nonlocal best
  order=[];bounds=[];Q=P;c=0
  while Q:
   c+=1;A=Q
   while A:
    b=A&-A;v=b.bit_length()-1;order.append(v);bounds.append(c);Q^=b;A^=b;A&=~adj[v]
  for i in range(len(order)-1,-1,-1):
   if s+bounds[i]<=best:return
   v=order[i];b=1<<v
   if P&b:
    p=P&adj[v]
    if p:go(p,s+1)
    else:best=max(best,s+1)
    P^=b
 go((1<<len(adj))-1,0);return best
for n in range(1,9):
 for k in range(2,9):
  maxima=[]
  for m in range(k):
   vs=[s for s in range(1<<n) if s.bit_count()%k==m]
   adj=[sum(1<<j for j,b in enumerate(vs) if a!=b and (a&b).bit_count()%k==m) for a in vs]
   maxima.append(clique(adj))
  out.append({'n':n,'k':k,'maximum_sizes_by_residue':maxima,'monotone':all(a>=b for a,b in zip(maxima,maxima[1:]))})
print('checks',len(out),'violations',[x for x in out if not x['monotone']])
(Path(__file__).parent/'bounded-checks.json').write_text(json.dumps({'route':370667,'executed':'Exact maximum-clique branch and bound on all admissible subsets; n=1..8,k=2..8. Strict cardinality convention, empty families allowed. No asymptotic inference.','results':out,'wall_seconds':time.monotonic()-start,'proof_scope':'finite instances only; not a full-scope proof or novelty clearance'},indent=2)+'\n')
