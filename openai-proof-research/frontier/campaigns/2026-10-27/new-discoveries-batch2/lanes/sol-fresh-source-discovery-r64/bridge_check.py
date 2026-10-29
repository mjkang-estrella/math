import json,itertools
from fractions import Fraction as F
from pathlib import Path
# Import functions without executing the experiment dispatch.
ns={'__file__':'check.py'};exec(Path('check.py').read_text().split("mode=sys.argv")[0],ns)
det,coeff=ns['det'],ns['coeff']
def inv(A):
 n=len(A);B=[[F(x) for x in r]+[F(i==j) for j in range(n)] for i,r in enumerate(A)]
 for k in range(n):
  z=next(i for i in range(k,n) if B[i][k]);B[k],B[z]=B[z],B[k];p=B[k][k];B[k]=[x/p for x in B[k]]
  for i in range(n):
   if i!=k:
    p=B[i][k];B[i]=[x-p*y for x,y in zip(B[i],B[k])]
 return [r[n:] for r in B]
counts={'kernel_coefficients':0,'complementary_minors':0,'permutation_determinants':0,'known_period_values':0,'known_linear_subsequence':0}
for n in [1,2,3]:
 f=coeff(n,90);ell=n+1
 for m in range(1,19):
  H=[[f[ell+i+j] for j in range(m)] for i in range(m)];delta=det(H)
  if abs(delta)!=1:continue
  B=inv(H);b=[B[i][-1] for i in range(m)];c=[-sum(B[i][j]*f[ell+m+j] for j in range(m)) for i in range(m)]+[F(1)]
  def cv(v,i):return v[i] if 0<=i<len(v) else F(0)
  # (x-y) K = p(x)b(y)-b(x)p(y), including the outer boundary.
  for i in range(m+1):
   for j in range(m+1):
    lhs=(B[i-1][j] if i>0 and j<m else 0)-(B[i][j-1] if j>0 and i<m else 0)
    assert lhs==cv(c,i)*cv(b,j)-cv(b,i)*cv(c,j)
    counts['kernel_coefficients']+=1
  for t in range(1,7):
   a=t//2;z=t-a
   for j in range(max(0,m-6),m+1):
    if j+max(a,z)>m:continue
    I=list(range(a,a+j));J=list(range(z,z+j));Ic=[i for i in range(m) if i not in I];Jc=[i for i in range(m) if i not in J]
    left=det([[f[ell+t+i+k] for k in range(j)] for i in range(j)])
    right=(-1)**(sum(I)+sum(J))*delta*det([[B[i][k] for k in Ic] for i in Jc])
    assert left==right
    counts['complementary_minors']+=1
 for m in range(1,6):
  A=[[f[n+3+i+j] for j in range(m)] for i in range(m)]
  d=0
  for perm in itertools.permutations(range(m)):
   v=(-1)**sum(perm[i]>perm[j] for i in range(m) for j in range(i+1,m))
   for i,j in enumerate(perm):v*=A[i][j]
   d+=v
  assert d==det(A);counts['permutation_determinants']+=1
for n in [1,2]:
 data=json.loads(Path('checks-hankel-'+str(n)+'.json').read_text());rows={r['shift']:r['values'] for r in data['rows']};rho=data['rho']
 d=rows[n+2]
 assert all(d[j]==d[j+rho] for j in range(len(d)-rho));counts['known_period_values']+=len(d)-rho
 P=2*n*(n+1)
 for k in range(1,4):
  want=(-1)**k*2*k if n==1 else (-1)**(n*k)*(4*n+2)*k
  assert rows[n+3][P*k-1]==want;counts['known_linear_subsequence']+=1
Path('checks-bridge.json').write_text(json.dumps({'status':'PASS','counts':counts,'claim':'Finite exact validation of classical identities only; no universal source resolution'},indent=2)+'\n')
print(counts)
