# Exact verification of a facet certificate for P_Delta^{p,q,r} (no-three-way interaction model [12][13][23]).
# P = cone over columns col(i,j,k) = e_{12:(i,j)} + e_{13:(i,k)} + e_{23:(j,k)} in R^{pq+pr+qr}.
# Certificate: linear functional l = (a_ij, b_ik, c_jk) with l(col(i,j,k)) = a_ij+b_ik+c_jk >= 0 for all cells
# (valid), and rank{col(i,j,k): tight} = rank{all columns} - 1 (facet), all ranks exact over Q (Fraction).
import sys,json,itertools
sys.path.insert(0,__import__('os').path.dirname(__file__)); from coarse import trees,vertices
from fractions import Fraction
def rank_exact(rows):
  A=[list(map(Fraction,r)) for r in rows]; r=0; n=len(A[0]) if A else 0
  for c in range(n):
    piv=next((i for i in range(r,len(A)) if A[i][c]!=0),None)
    if piv is None: continue
    A[r],A[piv]=A[piv],A[r]
    for i in range(len(A)):
      if i!=r and A[i][c]!=0:
        f=A[i][c]/A[r][c]; A[i]=[x-f*y for x,y in zip(A[i],A[r])]
    r+=1
  return r
def certify(a,p,q,slices):
  r=len(slices); 
  idx={}; 
  for i in range(p):
    for j in range(q): idx[('12',i,j)]=len(idx)
  for i in range(p):
    for k in range(r): idx[('13',i,k)]=len(idx)
  for j in range(q):
    for k in range(r): idx[('23',j,k)]=len(idx)
  n=len(idx); cols={}; val={}
  for i,j,k in itertools.product(range(p),range(q),range(r)):
    v=[0]*n; v[idx[('12',i,j)]]=1; v[idx[('13',i,k)]]=1; v[idx[('23',j,k)]]=1; cols[(i,j,k)]=v
    u,w=slices[k]; val[(i,j,k)]=a[i][j]+u[i]+w[j]
  valid=all(x>=0 for x in val.values())
  tight=[c for c,x in val.items() if x==0]
  D=rank_exact(list(cols.values())); Rt=rank_exact([cols[c] for c in tight])
  pats=[frozenset((i,j) for i in range(p) for j in range(q) if val[(i,j,k)]==0) for k in range(r)]
  return dict(p=p,q=q,r=r,ambient=n,dim_cone=D,expected_dim=p*q+p*r+q*r-p-q-r+1,valid=valid,tight_cells=len(tight),rank_tight=Rt,
              is_facet=valid and Rt==D-1,distinct_slice_patterns=len(set(pats))==r,
              functional=dict(a=[[str(x) for x in row] for row in a],b=[[str(slices[k][0][i]) for k in range(r)] for i in range(p)],c=[[str(slices[k][1][j]) for k in range(r)] for j in range(q)]),
              slice_zero_patterns=[sorted(pt) for pt in pats])
if __name__=='__main__':
  a=json.loads(sys.argv[1]); p,q=len(a),len(a[0]); V=vertices([[Fraction(x) for x in row] for row in a],p,q,trees(p,q))
  sl=sorted(V.keys()); res=certify(a,p,q,sl)
  print(json.dumps(res))
