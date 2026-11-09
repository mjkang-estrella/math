import itertools,json,pathlib,sys
import numpy as np
from scipy.optimize import milp,LinearConstraint,Bounds
D=pathlib.Path(__file__).resolve().parents[1]
# Exact feasibility on the half-integral unit l1 sphere in dimension 3.
vectors=[v for v in itertools.product(range(-2,3),repeat=3) if sum(map(abs,v))==2]
n=int(sys.argv[1]);edges=[(i,(i+1)%n) for i in range(n)]+[(i,n+i) for i in range(n)]+[(n+i,n+(i+2)%n) for i in range(n)]
# Generalized Petersen(n,2); n=5 is Petersen. One binary choice per edge/vector.
A=np.zeros((len(edges)+6*n,len(edges)*len(vectors)));target=np.zeros(A.shape[0]);target[:len(edges)]=1
for k,(a,b) in enumerate(edges):
 for z,v in enumerate(vectors):
  j=k*len(vectors)+z;A[k,j]=1
  for c in range(3):A[len(edges)+3*a+c,j]=v[c];A[len(edges)+3*b+c,j]=-v[c]
r=milp(np.zeros(A.shape[1]),integrality=np.ones(A.shape[1]),bounds=Bounds(0,1),constraints=LinearConstraint(A,target,target),options={'time_limit':30,'threads':1})
cert=None
if r.x is not None:
 z=np.rint(r.x).astype(int)
 if np.array_equal(A@z,target):cert=[vectors[next(i for i in range(len(vectors)) if z[k*len(vectors)+i])] for k in range(len(edges))]
out=dict(graph=f'GP({n},2)',edges=edges,unit_vectors_scaled_by=2,status=int(r.status),message=r.message,certificate=cert,limitation='Infeasibility only rules out half-integral unit flows, not real flows; status1 timeout has no negative implication.')
(D/f'outputs/flow-gp{n}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
