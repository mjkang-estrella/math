"""Exact finite verification, independent of the ordinary proof in PROOF.md."""
from pathlib import Path
from itertools import combinations
import json
L=Path(__file__).resolve().parent
def inspect(k,cycle=False):
 n=2*k
 edges=[(v,v+k) for v in range(k)]+[(v,v+1) for v in range(k-1)]
 if cycle:edges.append((0,k-1))
 adj=[0]*n
 for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
 full=(1<<n)-1;mins=n;icount=0
 for s in range(1<<n):
  if any(s>>v&1 and adj[v]&s for v in range(n)):continue
  d=s
  for v in range(n):
   if s>>v&1:d|=adj[v]
  if d==full:mins=min(mins,s.bit_count());icount+=1
 mm=len(edges);mc=0
 # Enumerate literal edge subsets; maximal iff unmatched vertices independent.
 for s in range(1<<len(edges)):
  used=0;valid=True
  for j,(u,v) in enumerate(edges):
   if s>>j&1:
    b=(1<<u)|(1<<v)
    if used&b:valid=False;break
    used|=b
  if valid and all(used>>u&1 or used>>v&1 for u,v in edges):
   mm=min(mm,s.bit_count());mc+=1
 deg=[x.bit_count() for x in adj]
 assert mins==k and mm==(k+1)//2
 return dict(core=('cycle' if cycle else 'path'),k=k,vertices=n,edges=edges,i=mins,mu_star=mm,delta=min(deg),Delta=max(deg),independent_dominating_sets=icount,maximal_matchings=mc,violates=mins>mm+max(deg)-min(deg))
r=[inspect(k) for k in range(2,9)]+[inspect(6,True)]
assert next(x for x in r if x['core']=='path' and x['k']==6)['violates']
(L/'check-results.json').write_text(json.dumps(dict(status='PASS',cases=r,arithmetic='integer exhaustive vertex/edge subsets; no probabilistic or floating-point decisions',proof_status='finite verification only; full mathematical refutation separately proved'),indent=2)+'\n')
print('PASS',len(r),'literal graphs; path-corona order12 refutes claimed inequality')
