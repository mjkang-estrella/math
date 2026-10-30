"""Exact diagnostic of an explicitly public refutation; no new theorem claimed."""
import itertools,json
from pathlib import Path
L=Path(__file__).resolve().parent
def adjacency(n):
 # (i,e)=a^i b^e; multiply (i,e)(j,f)=(i+(-1)^e*j,e+f).
 return [{2*((i+(-1 if e else 1)*j)%n)+(e^1) for j in (0,1,3)} for i in range(n) for e in range(2)]
adj=adjacency(9); witness=None;tested=0
for U in itertools.combinations(range(18),10):
 tested+=1;s=set(U)
 if all(len(adj[v]&s)==1 for v in U):witness=list(U);break
assert witness is not None
rows=[]
for m in range(1,13):
 a=adjacency(9*m);U={2*i+e for i in range(9*m) for e in (0,1) if 2*(i%9)+e in witness}
 deg=[len(a[v]&U) for v in sorted(U)]
 assert len(U)==10*m and min(deg)==max(deg)==1 and 2*len(U)>18*m
 rows.append(dict(m=m,order=18*m,subset_size=len(U),minimum_induced_degree=min(deg),maximum_induced_degree=max(deg)))
out=dict(status='DIAGNOSTIC ONLY: public Lehner-Verret Section 3',convention='right Cayley multiplication; inversion maps to source left convention',witness=[[v//2,v%2] for v in witness],tested_until_first=tested,controls=rows,exact_violation='degree 1; d=3; 1^2 < 3/2',universal_gap='none for the cited public dihedral family via local-cover proof; general conjecture already false; no new eligible result')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
