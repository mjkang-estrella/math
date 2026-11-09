from explore import *
import numpy as np,itertools
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
def ts(n):return [(x-1,y-1,x+y//2-1) for x in range(1,n+1) for y in range(1,n+1) if x+y//2<=n]
out=[]
for n in [12,13,18,24,30]:
 triples=ts(n);edges=list(itertools.combinations(range(n),2));ei={e:i for i,e in enumerate(edges)};w=np.zeros(len(edges),dtype=np.int64)
 for t in triples:
  for a,b in itertools.combinations(t,2):
   if a!=b:w[ei[tuple(sorted((a,b)))]]+=1
 triangles=list(itertools.combinations(range(n),3));rows=[];cols=[]
 for j,t in enumerate(triangles):
  for e in itertools.combinations(t,2):rows.append(ei[e]);cols.append(j)
 A=coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(len(edges),len(triangles))).tocsr()
 sol=linprog(-np.ones(len(triangles)),A_ub=A,b_ub=w,bounds=(0,None),method='highs',options={'time_limit':35,'threads':1})
 packing=-sol.fun if sol.success else None
 ub=float(sum(w)-packing) if packing else None
 # A triangle packing bounds cut by total edge weight minus packing.
 lower=(len(triples)-ub/2) if ub else None
 rec=dict(n=n,status=sol.message,triangle_packing=packing,implied_M_lower=lower,target=(n*n+5)//6,total_edge_weight=int(sum(w)))
 out.append(rec);print(rec,flush=True)
(L/'triangle-packing.json').write_text(json.dumps(out,indent=2))
