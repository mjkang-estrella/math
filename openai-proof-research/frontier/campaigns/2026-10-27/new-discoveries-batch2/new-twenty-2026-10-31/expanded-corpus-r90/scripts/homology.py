from pathlib import Path
from itertools import combinations
import json,sys
D=Path(__file__).resolve().parents[1]
def rank2(columns):
 basis={}
 for v in columns:
  while v:
   p=v.bit_length()-1
   if p in basis:v^=basis[p]
   else:basis[p]=v;break
 return len(basis)
def run(n):
 N=n+1;edges=[(i,(i+1)%N) for i in range(N)]+[((i+1)%N,i) for i in range(N)];edges.pop();M=len(edges)
 conflicts=[]
 for i,(a,b) in enumerate(edges):
  conflicts.append(sum(1<<j for j,(c,d) in enumerate(edges) if j!=i and (a==c or b==d or (a==d and b==c))))
 levels=[[] for _ in range(N)]
 def rec(mask,start):
  # at most one directed cycle possible: full polygon
  if mask.bit_count()==N:return
  levels[mask.bit_count()].append(mask)
  for j in range(start,M):
   if not mask&conflicts[j]:rec(mask|1<<j,j+1)
 rec(0,0);ranks=[0]*N
 for k in range(2,N):
  idx={m:i for i,m in enumerate(levels[k-1])}
  def cols():
   for m in levels[k]:
    v=0
    for j in range(M):
     if m>>j&1:v^=1<<idx[m^(1<<j)]
    yield v
  ranks[k]=rank2(cols())
 ranks[1]=0
 betti={str(k-1):len(levels[k])-ranks[k]-(ranks[k+1] if k+1<N else 0) for k in range(1,N)}
 # H0 boundary rank d1 = vertex count minus components; rank2 above handles d1 at k2
 recd={'n':n,'polygon_vertices':N,'directed_edges':M,'f_vector':[len(x) for x in levels[1:]],'betti_F2':{k:v for k,v in betti.items() if v},'scope':'exact F2 boundary ranks; no integral torsion certificate'}
 (D/f'outputs/homology-{n}.json').write_text(json.dumps(recd,indent=2)+'\n');print(recd,flush=True)
for n in map(int,sys.argv[1:]):run(n)
