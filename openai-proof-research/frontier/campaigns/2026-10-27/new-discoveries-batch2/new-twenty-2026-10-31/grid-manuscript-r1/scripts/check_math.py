from itertools import product
from collections import Counter
from pathlib import Path
import json

def parts(n):
 def gen(a):
  if len(a)==n: yield tuple(a); return
  for c in range(max(a,default=-1)+2): yield from gen(a+[c])
 return list(gen([]))
def grid(m,n):
 V=list(product(range(m),range(n))); idx={v:i for i,v in enumerate(V)}
 N=[[idx[w] for w in V if abs(v[0]-w[0])+abs(v[1]-w[1])==1] for v in V]
 return V,N
results=[]
for m,n in [(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,4)]:
 V,N=grid(m,n); idx={v:i for i,v in enumerate(V)}; maps=set()
 for a,b,t in product(range(2),repeat=3):
  if t and m!=n: continue
  out=[]
  for i,j in V:
   if t: i,j=j,i
   if a: i=m-1-i
   if b: j=n-1-j
   out.append(idx[i,j])
  maps.add(tuple(out))
 maps=sorted(maps); identity=tuple(range(len(V))); one=maps.index(identity)
 mul=[[maps.index(tuple(g[h[i]] for i in range(len(V)))) for h in maps] for g in maps]
 subs=[tuple(i for i in range(len(maps)) if mask>>i&1) for mask in range(1<<len(maps)) if mask>>one&1]
 subs=[H for H in subs if all(mul[a][b] in H for a in H for b in H)]
 def orbits(H):
  cells=[min(maps[g][v] for g in H) for v in range(len(V))]
  return tuple(cells)
 orbitsets={orbits(H) for H in subs}
 exhaustive=m*n<=12
 eq=set()
 if exhaustive:
  groups=[[i for i in range(len(V)) if len(N[i])==d] for d in sorted({len(x) for x in N})]
  for choices in product(*(parts(len(g)) for g in groups)):
   labels=[None]*len(V)
   for d,(g,a) in enumerate(zip(groups,choices)):
    for v,c in zip(g,a): labels[v]=(d,c)
   rule={}; ok=True
   for v in range(len(V)):
    sig=Counter(labels[w] for w in N[v]); c=labels[v]
    if c in rule and rule[c]!=sig: ok=False; break
    rule[c]=sig
   if ok: eq.add(tuple(min(i for i in range(len(V)) if labels[i]==labels[v]) for v in range(len(V))))
  assert eq==orbitsets
 expected={(1,1):(1,1),(1,2):(2,2),(1,3):(2,2),(2,2):(7,10),(2,3):(5,5),(3,3):(9,10),(3,4):(5,5),(4,4):(10,10)}[m,n]
 assert (len(orbitsets),len(subs))==expected
 results.append({'grid':[m,n],'equitable_exhaustive':len(eq) if exhaustive else None,'orbit_partitions':len(orbitsets),'explicit_group_subgroups':len(subs),'exhaustive_degree_pruned':exhaustive})
Path('receipts/math-check.json').write_text(json.dumps({'note':'Diagnostic only. Explicit reflection group used, not an independent enumeration of full Aut; 4x4 equitable count follows the ordinary theorem rather than enumeration.','results':results},indent=2)+'\n')
print(results)
