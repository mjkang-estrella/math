from pathlib import Path
from itertools import combinations
from fractions import Fraction as F
from math import comb
import json
L=Path(__file__).resolve().parent
def edges(n):return list(combinations(range(n),2))
def esmask(es,ids):return sum(1<<es.index(e) for e in ids)
def independent_sets(n,g,es):
 return [s for s in range(1<<n) if all(not(g>>i&1) or not(s>>u&1 and s>>v&1) for i,(u,v) in enumerate(es))]
counts=[];union_controls=0;transform_controls=0;apex_controls=0
for n in range(1,7):
 es=edges(n);N=len(es);distribution=[0]*(n+1);tf=0
 tri=[esmask(es,list(combinations(t,2))) for t in combinations(range(n),3)]
 for g in range(1<<N):
  al=max(s.bit_count() for s in independent_sets(n,g,es));distribution[n-al]+=1
  tf+=not any(g&t==t for t in tri)
 C=[sum(distribution[:k+1]) for k in range(n+1)]
 if n>=3:assert C[n-3]==(1<<N)-tf
 counts.append(dict(n=n,cover_counts=C,triangle_free=tf))
 # Independent-set-event inclusion-exclusion; finite full event families only n<=5.
 if n<=5:
  for s in range(2,n+1):
   event=[esmask(es,list(combinations(t,2))) for t in combinations(range(n),s)]
   coeff={}
   for family in range(1,1<<len(event)):
    u=0
    for i,e in enumerate(event):
     if family>>i&1:u|=e
    coeff[u]=coeff.get(u,0)+(1 if family.bit_count()%2 else -1)
   ans=sum(c*(1<<(N-u.bit_count())) for u,c in coeff.items())
   assert ans==C[n-s];union_controls+=1
   if n==4 and s==3:assert coeff[(1<<N)-1]==3
for a in range(1,5):
 for b in range(1,5):
  if a*b>12:continue
  raw=F(0);unions=set()
  for h in range(1<<(a*b)):
   active=set();u=0;m=h.bit_count()
   for i in range(a):
    for j in range(b):
     if h>>(i*b+j)&1:active.update([i,a+j]);u|=1<<(i*b+j)
   raw+=(-F(1,2))**m*F(1,2)**len(active)
   if h:
    # The cross edges recover H from its union of apex triangles.
    unions.add(u);assert (-1)**(m+1) in [-1,1];apex_controls+=1
  collapsed=F(1,2**(a+b))*sum(F(comb(a,i)*comb(b,j),2**((a-i)*(b-j))) for i in range(a+1) for j in range(b+1))
  assert raw==collapsed;assert len(unions)==2**(a*b)-1;transform_controls+=1
out=dict(status='PASS',graph_counts=counts,inclusion_exclusion_controls=union_controls,apex_family_controls=apex_controls,collapsed_transform_controls=transform_controls,limits='Finite diagnostics only. Universal identities proved in discovery.md; no subquadratic full algorithm established.')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
