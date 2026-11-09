import json,itertools
from pathlib import Path
p=Path(__file__).resolve().parent;d=json.loads((p/'reversal-priority-obstruction.json').read_text());n=12
R={tuple(x) for x in d['relations']};C=d['chains'];inc=[(a,b) for a in range(n) for b in range(a+1,n) if (a,b) not in R and (b,a) not in R]
assert not any((x,x) in R for x in range(n))
assert all((a,c) in R for a,b in R for bb,c in R if b==bb)
assert sorted(sum(C,[]))==list(range(n))
assert all((a,b) in R for chain in C for i,a in enumerate(chain) for b in chain[i+1:])
assert all((a,b) not in R and (b,a) not in R for a,b in itertools.combinations([1,5,9],2))
assert [list(x) for x in inc]==d['incomparables'] and len(inc)==19
orders=d['priority_orders'];co={x:i for i,chain in enumerate(C) for x in chain}
for L,priority in zip(orders,itertools.permutations(range(3))):
 remain=set(range(n));rank={c:i for i,c in enumerate(priority)}
 for x in L:
  available=[v for v in remain if not any((u,v) in R for u in remain)]
  assert x==min(available,key=lambda v:(rank[co[v]],v));remain.remove(x)
def positions(L):
 assert sorted(L)==list(range(n));pos={x:i for i,x in enumerate(L)}
 assert all(pos[a]<pos[b] for a,b in R);return pos
def dist(L,M):
 a,b=positions(L),positions(M)
 return sum((a[x]<a[y])!=(b[x]<b[y]) for x,y in inc)
matrix=[[dist(L,M) for M in orders] for L in orders]
assert max(map(max,matrix))==14
assert dist(*d['diametral_pair'])==19
report=dict(width=3,inc=19,priority_distance_matrix=matrix,priority_diameter=14,unrestricted_diameter=19,all_assertions_passed=True)
(p/'obstruction-verification.json').write_text(json.dumps(report,indent=2));print(json.dumps(report))
