"""Exact finite diagnostics. No universal assertion is established by these tests."""
import os,resource,signal
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,45));signal.alarm(50)
from fractions import Fraction as F
from itertools import combinations
import random,json,datetime
from pathlib import Path

def solve(A,b):
 A=[[F(x) for x in r]+[F(y)] for r,y in zip(A,b)];n=len(b)
 for j in range(n):
  p=next((i for i in range(j,n) if A[i][j]),None)
  if p is None:return None
  A[j],A[p]=A[p],A[j];z=A[j][j];A[j]=[x/z for x in A[j]]
  for i in range(n):
   if i!=j:
    z=A[i][j];A[i]=[x-z*y for x,y in zip(A[i],A[j])]
 return [r[-1] for r in A]
def dot(a,b):return sum((x*y for x,y in zip(a,b)),F(0))
def profile(V,p,e):
 V=[list(map(F,r)) for r in V];p=list(map(F,p));p=[v/sum(p) for v in p];e=list(map(F,e));n=len(V)
 assert all(v>0 for v in p)
 assert all(sum(p[i]*V[i][j]*e[i] for i in range(n))==0 for j in range(3))
 L=sum(p[i]*e[i]**2 for i in range(n));assert L>0
 M=[[sum(p[a]*V[a][i]*V[a][j] for a in range(n))/L for j in range(3)] for i in range(3)]
 # Exact Sylvester positivity using LDL pivots.
 assert M[0][0]>0 and M[0][0]*M[1][1]-M[0][1]**2>0
 assert solve(M,[1,0,0]) is not None
 def inn(a,b):return sum(a[i]*M[i][j]*b[j] for i in range(3) for j in range(3))
 bases={T:solve([V[i] for i in T],[e[i] for i in T]) for T in combinations(range(n),3)}
 bases={T:q for T,q in bases.items() if q is not None};assert bases
 x=min(inn(q,q) for q in bases.values());y=x;faces=0
 for T in combinations(range(n),4):
  Q=[bases[S] for S in combinations(T,3) if S in bases]
  for size in range(1,len(Q)+1):
   for J in combinations(range(len(Q)),size):
    P=[Q[j] for j in J];G=[[inn(a,b) for b in P] for a in P]
    z=solve([r+[F(1)] for r in G]+[[F(1)]*size+[F(0)]],[F(0)]*size+[F(1)])
    if z is None or min(z[:size])<0:continue
    q=[sum(z[i]*P[i][j] for i in range(size)) for j in range(3)];y=min(y,inn(q,q));faces+=1
 # Independent check: arbitrary weights yield convex combination of adjacent interpolants.
 identities=0
 for T in combinations(range(n),4):
  Q={i:bases[tuple(j for j in T if j!=i)] for i in T if tuple(j for j in T if j!=i) in bases}
  if not Q:continue
  # h_i=(-1)^i det(V with i omitted), computed via 3x3 formula.
  def det(A):return sum(A[0][i]*(A[1][(i+1)%3]*A[2][(i+2)%3]-A[1][(i+2)%3]*A[2][(i+1)%3]) for i in range(3))
  h={i:(-1)**j*det([V[a] for a in T if a!=i]) for j,i in enumerate(T)}
  alpha={i:F(j+1) for j,i in enumerate(T)}
  H=[[sum(alpha[a]*V[a][i]*V[a][j] for a in T) for j in range(3)] for i in range(3)]
  b=[sum(alpha[a]*V[a][j]*e[a] for a in T) for j in range(3)];u=solve(H,b)
  lam={i:h[i]**2/alpha[i] for i in Q};total=sum(lam.values())
  q=[sum(lam[i]*Q[i][j] for i in Q)/total for j in range(3)];assert u==q;identities+=1
 return dict(V=V,p=p,e=e,L=L,x=x,y=y,facet=2*x+3*y,passes=2*x+3*y<=6,bases=len(bases),faces=faces,normal_equation_identities=identities)

rng=random.Random(29102602);out=[]
# Uniform simplex baseline; arbitrary nonuniform labels on a circuit.
for masses in [[1,1,1,1],[1,2,3,7],[100,1,2,1]]:
 V=[[1,0,0],[0,1,0],[0,0,1],[-1,-1,-1]]
 e=[F(1,m) for m in masses];out.append(profile(V,masses,e))
# Arbitrary residuals by exact weighted projection; do not impose equal labels/mean-zero rows.
for n in [5,6,7]:
 for trial in range(5):
  V=[[rng.randint(-3,3) for j in range(3)] for i in range(n)]
  V[:3]=[[1,0,0],[0,1,0],[0,0,1]]
  if trial==1:V[-1]=V[0][:] # repeated row, possibly different label
  p=[rng.randint(1,9) for i in range(n)];a=[F(rng.randint(-4,4)) for i in range(n)]
  H=[[sum(p[i]*V[i][j]*V[i][k] for i in range(n)) for k in range(3)] for j in range(3)]
  b=[sum(p[i]*V[i][j]*a[i] for i in range(n)) for j in range(3)];w=solve(H,b)
  e=[a[i]-dot(V[i],w) for i in range(n)]
  if any(e):out.append(profile(V,p,e))
# Exact zero-label anchors; two opposite pairs plus a zero-label independent direction.
for masses in [[1,2,3,4,5],[9,1,2,7,3]]:
 V=[[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1]]
 e=[F(1,masses[0]),F(1,masses[1]),F(2,masses[2]),F(2,masses[3]),F(0)]
 out.append(profile(V,masses,e))
assert out[0]['x']==3 and out[0]['y']==0
assert all(z['passes'] for z in out)
# Nonzero-label transformation: masses become p_i e_i^2/L, rows V_i/e_i;
# its total mass is one only when zero labels make no covariance contribution.
transforms=0
for z in out:
 if all(z['e']):
  V=z['V'];p=z['p'];e=z['e'];L=z['L']
  mass=[p[i]*e[i]**2/L for i in range(len(V))];rows=[[v/e[i] for v in r] for i,r in enumerate(V)]
  assert sum(mass)==1
  assert all(sum(mass[i]*rows[i][j] for i in range(len(V)))==0 for j in range(3))
  assert all(sum(mass[a]*rows[a][i]*rows[a][j] for a in range(len(V)))==sum(p[a]*V[a][i]*V[a][j]/L for a in range(len(V))) for i in range(3) for j in range(3));transforms+=1
result=dict(status='PASS_FINITE_DIAGNOSTICS_ONLY',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seed=29102602,limits=dict(AS=536870912,CPU=45,wall=50,BLAS=1),profiles=out,nonzero_label_transforms=transforms)
Path(__file__).with_name('checks.json').write_text(json.dumps(result,default=str,indent=2))
print('PASS',len(out),'profiles;',sum(z['normal_equation_identities'] for z in out),'normal-equation identities;',transforms,'mass/label transformations')
print('Largest facet',max(z['facet'] for z in out))
