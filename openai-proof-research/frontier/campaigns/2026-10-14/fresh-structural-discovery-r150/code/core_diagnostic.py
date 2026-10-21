"""Bounded exact diagnostic; does not prove mixing or uniform variable-surplus sampling."""
from pathlib import Path
from itertools import combinations,product
from collections import Counter
from math import factorial,prod
from fractions import Fraction
import json
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-structural-discovery-r150')
def connected(n,edges):
 adj=[set() for _ in range(n)]
 for a,b in edges: adj[a].add(b);adj[b].add(a)
 seen={0}; todo=[0]
 while todo:
  for v in adj[todo.pop()]-seen: seen.add(v);todo.append(v)
 return len(seen)==n,adj
def core(adj):
 C=set(range(len(adj)))
 while True:
  bad={v for v in C if len(adj[v]&C)<2}
  if not bad:return tuple(sorted(C))
  C-=bad
obs=[]
for n in range(3,7):
 es=list(combinations(range(n),2)); grouped=Counter(); degcounts=Counter(); ct=0
 for mask in range(1<<len(es)):
  edges=tuple(e for j,e in enumerate(es) if mask>>j&1)
  yes,adj=connected(n,edges)
  if not yes:continue
  ct+=1;d=tuple(map(len,adj));C=core(adj)
  if C:
   h=tuple(e for e in edges if e[0] in C and e[1] in C)
   grouped[d,C,h]+=1
  if len(edges)==n:degcounts[d]+=1
 for (d,C,h),number in grouped.items():
  m=n-len(C);s=Counter(v for e in h for v in e)
  c=[d[v]-s[v] if v in C else d[v]-1 for v in range(n)]
  assert sum(c)==m
  A=sum(c[v] for v in C)
  expected=Fraction(factorial(m-1)*A,prod(factorial(x) for x in c)) if m else 1
  assert number==expected,(n,d,C,h,number,expected)
 for d,number in degcounts.items():
  result=Fraction(0);eligible=[i for i in range(n) if d[i]>=2]
  for k in range(3,n+1):
   for C in combinations(eligible,k):
    m=n-k
    if not m:
     if all(x==2 for x in d):result+=Fraction(factorial(n-1),2)
     continue
    A=sum(d[i]-2 for i in C)
    result+=Fraction(factorial(k-1)*factorial(m-1)*A*prod(d[i]-1 for i in C),2*prod(factorial(x-1) for x in d))
  assert result==number,(d,result,number)
 obs.append(dict(n=n,graphs_checked=1<<len(es),connected=ct,core_fibers=len(grouped),unicyclic_degree_vectors=len(degcounts)))
checks=0;mapcount=0
for n in range(2,6):
 for k in range(1,n):
  # Symmetry allows a single fixed root set for each n,k.
  C=set(range(k));U=list(range(k,n));m=n-k;counts=Counter();forests=Counter()
  for values in product(range(n),repeat=m):
   c=tuple(values.count(i) for i in range(n));counts[c]+=1;mapcount+=1
   parent=dict(zip(U,values));ok=True
   for v in U:
    seen=set()
    while v not in C:
     if v in seen:ok=False;break
     seen.add(v);v=parent[v]
    if not ok:break
   if ok:forests[c]+=1
  for c,ct in counts.items():
   assert ct==factorial(m)//prod(factorial(x) for x in c)
   assert Fraction(forests[c],ct)==Fraction(sum(c[:k]),m)
   checks+=1
out={'scope':'Exact finite diagnostics only; no mathematical gate','core_and_unicyclic_checks':obs,'parent_maps':mapcount,'parent_count_fibers':checks}
(R/'notes/finite-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
