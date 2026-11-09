from fetch import *
import itertools,math
import numpy as np
from scipy.spatial import ConvexHull
A=np.array([[0,0,0,0],[0,0,0,1],[0,0,1,1],[0,1,1,0]],dtype=int)
B=np.array([[0,0,0,0,0],[-1,0,0,0,0],[-1,-1,-1,0,0],[0,-1,0,-1,0]])
C=np.array([[1,1,1,1,0],[1,1,1,0,0],[1,0,0,0,0],[0,1,0,1,0]])
W=A[:,:,None]+B[:,None,:]+C[None,:,:]
z=[[(i,j) for i in range(4) for j in range(4) if W[i,j,k]==0] for k in range(5)]
# Independent floating hull used only to enumerate, exact reconstruction checked below.
pts=np.array([[int(i==t) for t in range(1,4)]+[int(j==t) for t in range(1,4)]+[int(A[i,j])] for i in range(4) for j in range(4)])
h=ConvexHull(pts);lower=set()
for eq in h.equations:
 if eq[-2]<-1e-7:lower.add(tuple(np.where(abs(pts@eq[:-1]+eq[-1])<1e-7)[0]))
assert lower==set(tuple(4*i+j for i,j in s) for s in z)
# Exact exhaustive supporting-hyperplane enumeration via all spanning trees of K44.
# Solve potentials on tree by propagation; no numeric decisions.
vertices=set()
for edges in itertools.combinations(range(16),7):
 u=[None]*8;u[0]=0
 for _ in range(7):
  for e in edges:
   i,j=divmod(e,4);j+=4
   if u[i] is not None:u[j]=int(A[i,j-4])-u[i]
   elif u[j] is not None:u[i]=int(A[i,j-4])-u[j]
 if any(x is None for x in u):continue
 if all(u[i]+u[4+j]<=A[i,j] for i in range(4) for j in range(4)):vertices.add(tuple(u))
assert len(vertices)==5
assert {tuple([-int(B[i,k]) for i in range(4)]+[-int(C[j,k]) for j in range(4)]) for k in range(5)}==vertices
# Exact equality-space dimension (a,b,c) from all tight sets.
import sympy as sp
rows=[]
for k,s in enumerate(z):
 for i,j in s:
  r=[0]*56;r[4*i+j]=1;r[16+5*i+k]=1;r[36+5*j+k]=1;rows.append(r)
rank=sp.polys.matrices.DomainMatrix.from_Matrix(sp.Matrix(rows)).rank()
# Row/column shifts remove first row and column. Include transpose and scale normalization.
def norm(a):
 d=a-a[:,[0]]-a[[0],:]+a[0,0];g=math.gcd(*map(int,d.flatten()))
 return tuple(map(int,(d//(g or 1)).flatten()))
can=min(norm(a[list(p),:][:,list(q)]) for a in [A,A.T] for p in itertools.permutations(range(4)) for q in itertools.permutations(range(4)))
r={'height':A.tolist(),'maximal_cells':z,'maximal_cell_sizes':list(map(len,z)),'exact_support_vertices':sorted(vertices),'tight_equation_rank':rank,'secondary_cone_dimension_mod_affine':56-rank-12,'canonical_height_row_column_transpose_affine_positive_scale':can,'canonical_sha256':hashlib.sha256(json.dumps(can).encode()).hexdigest(),'method':'all 11440 seven-edge subsets, integer spanning-tree potential enumeration; hull only auxiliary'}
(BASE/'outputs/candidate-subdivision.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
