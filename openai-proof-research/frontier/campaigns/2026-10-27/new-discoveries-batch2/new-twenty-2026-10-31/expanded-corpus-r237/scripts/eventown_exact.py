from pathlib import Path
import itertools,json
L=Path(__file__).resolve().parents[1]
# n=6: even vectors pair with their complements. Their quotient has 16 vertices;
# each pair has identical external neighbours and no internal odd-intersection edge.
# For a fixed size there is an optimum with at most one singly used twin class:
# adjust two singles by (+1,-1) or (-1,+1). The sum of objective changes is
# -2*adjacency <=0, so one direction cannot increase the objective. Iterate.
V=[x for x in range(32) if x.bit_count()%2==0];A=[[((x&y).bit_count()%2) for y in V] for x in V];out=[]
for k in range(11,15):
 best=100000;checked=0;bestw=None;t=k//2
 for double in itertools.combinations(range(16),t):
  e=4*sum(A[x][y] for i,x in enumerate(double) for y in double[:i])
  singles=[None] if k%2==0 else [z for z in range(16) if z not in double]
  for z in singles:
   value=e+(2*sum(A[z][x] for x in double) if z is not None else 0);checked+=1
   if value<best:best=value;bestw={'doubled_classes':[V[x] for x in double],'single':None if z is None else V[z]}
 r={'n':6,'k':k,'s':k-8,'minimum':best,'bound':(k-8)*4,'reduced_families_checked':checked,'witness':bestw};out.append(r);print(r,flush=True)
(L/'outputs/eventown-exact.json').write_text(json.dumps(out,indent=2))
