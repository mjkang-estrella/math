"""Tiny finite checks of stated shortcut examples; not mathematical gates."""
from itertools import product, combinations
from pathlib import Path
import json
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct')
examples=[]
for t in range(2,15):
 n=2*t+1
 cycles=[]
 for i in range(t):
  v=[2*t,i]
  for j in range(1,t): v.extend([(i-j)%(2*t),(i+j)%(2*t)])
  v.append((i-t)%(2*t))
  assert len(v)==n and len(set(v))==n
  cycles.append(v)
 edges=[tuple(sorted((v[j],v[(j+1)%n]))) for v in cycles for j in range(n)]
 assert len(edges)==len(set(edges))==n*(n-1)//2
 assert set(edges)==set(combinations(range(n),2))
 examples.append({'n':n,'cycles':t,'wrong_mod3':n%3!=0,'discarded_edges':len(edges)})
# Three-cover of a cyclically oriented C4: voltage1 on every edge.
vertices=[(i%4,i%3) for i in range(12)]
assert len(set(vertices))==12
projected=[x for x,s in vertices]
assert projected==list(range(4))*3 and 12%3==0 and 4%3!=0
# Two-list colouring on even cycles, bounded sanity check only.
lists=list(combinations(range(3),2)); tested=0
for n in [4,6]:
 for choices in product(lists,repeat=n):
  assert any(all(c[i]!=c[(i+1)%n] for i in range(n)) for c in product(*choices))
  tested+=1
# Fixed-step residue arithmetic, including the parity limitation.
for q in range(2,22):
 s={(2*j)%q for j in range(q)}
 assert len(s)==q if q%2 else len(s)==q//2
out={'status':'finite sanity only; no mathematical gate','walecki':examples,'cover_vertices':vertices,'even_cycle_list_assignments':tested,'residue_moduli':20}
(R/'scratch/finite_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'walecki_orders':len(examples),'even_cycle_list_assignments':tested,'cover':12,'residue_moduli':20}))
