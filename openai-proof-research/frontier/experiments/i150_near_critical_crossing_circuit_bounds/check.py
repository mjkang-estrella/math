"""New finite rational checks only. No file, network, process or numerical-library access."""
from fractions import Fraction as F
from itertools import product
from collections import Counter

def prod(xs):
 r=F(1)
 for x in xs:r*=x
 return r

def solve(a,b):
 n=len(b);a=[list(r)+[b[i]] for i,r in enumerate(a)]
 for j in range(n):
  k=next(i for i in range(j,n) if a[i][j]);a[j],a[k]=a[k],a[j]
  z=a[j][j];a[j]=[x/z for x in a[j]]
  for i in range(n):
   if i!=j:
    z=a[i][j];a[i]=[x-z*y for x,y in zip(a[i],a[j])]
 return [r[-1] for r in a]

def run():
 counts=Counter()
 # Exact triangular geometry, reflection and three-colouring.
 dirs=((1,0),(0,1),(1,-1))
 for L in range(1,8):
  V={(i,j) for i in range(-2*L,2*L+1) for j in range(-2*L,2*L+1)}
  E={(x,(x[0]+a,x[1]+b)) for x in V for a,b in dirs if (x[0]+a,x[1]+b) in V}
  assert len(V)==(4*L+1)**2 and len(E)==48*L*L+8*L
  assert all((x[0]+2*x[1]-y[0]-2*y[1])%3 for x,y in E)
  und={frozenset(e) for e in E};assert {frozenset(( (x[1],x[0]),(y[1],y[0]) )) for x,y in E}==und
  counts['triangular_geometry_and_symmetry']+=1
 # All inner Lambda_1 assignments: spin flip plus axis exchange complements crossing.
 V=list(product(range(-1,2),repeat=2));idx={v:i for i,v in enumerate(V)}
 def cross(sig):
  seen={x for x in V if x[0]==-1 and sig[idx[x]]==1};stack=list(seen)
  while stack:
   x=stack.pop()
   for a,b in dirs+tuple((-a,-b) for a,b in dirs):
    y=(x[0]+a,x[1]+b)
    if y in idx and y not in seen and sig[idx[y]]==1:seen.add(y);stack.append(y)
  return any(x[0]==1 for x in seen)
 for sig in product((-1,1),repeat=9):
  transformed=tuple(-sig[idx[(y,x)]] for x,y in V)
  assert cross(sig)!=cross(transformed);counts['inner_crossing_complement']+=1
 # A non-diagonal rational observable, with rational orthonormal biased vectors.
 X=list(product((0,1),repeat=3));v=[(F(3,5),F(4,5)),(F(5,13),F(12,13)),(F(8,17),F(15,17))]
 w=[(b,-a) for a,b in v];prob={x:prod(v[i][x[i]]**2 for i in range(3)) for x in X}
 Q=[[F((i+1)*(j+1),1000) for j in range(8)] for i in range(8)]
 f={x:2*Q[ix][ix]-1 for ix,x in enumerate(X)};coeff={}
 for S in range(8):
  chi=lambda x:prod(w[i][x[i]]/v[i][x[i]] for i in range(3) if S>>i&1)
  coeff[S]=sum(prob[x]*f[x]*chi(x) for x in X)
  if S:
   phase=F(0)
   for h in X:
    bra=[prod((w[i] if S>>i&1 else v[i])[x[i]]*(-1)**(h[i]*x[i]) for i in range(3)) for x in X]
    ket=[prod(v[i][x[i]]*(-1)**(h[i]*x[i]) for i in range(3)) for x in X]
    phase+=sum(bra[i]*Q[i][j]*ket[j] for i in range(8) for j in range(8))/8
   assert coeff[S]==2*phase;counts['biased_phase_factor_two']+=1
 D=F(0)
 for i in range(3):
  for x in X:
   y=list(x);y[i]=1-x[i];y=tuple(y)
   D+=prob[x]*v[i][y[i]]**2*(f[x]-f[y])**2/2
 assert D==sum(S.bit_count()*a*a for S,a in coeff.items());counts['biased_dirichlet']+=1
 # Finite Ising triangle: physical form, conditional variances and resolvent minimizer.
 X=list(product((-1,1),repeat=3));where={x:i for i,x in enumerate(X)}
 for t in (F(0),F(1,4),F(2,3)):
  weights={x:prod(1+t*x[i]*x[j] for i,j in ((0,1),(0,2),(1,2))) for x in X}
  z=sum(weights.values());mu={x:a/z for x,a in weights.items()}
  A=[[F(0) for _ in X] for _ in X];Es=[]
  for i in range(3):
   Ei=[[F(0) for _ in X] for _ in X]
   for ix,x in enumerate(X):
    y=list(x);y[i]*=-1;y=tuple(y);iy=where[y];p=mu[y]/(mu[x]+mu[y])
    A[ix][ix]+=p;A[ix][iy]-=p;Ei[ix][ix]=1-p;Ei[ix][iy]=p
   Es.append(Ei)
  g=[F(1 if sum(x)>0 else -1) for x in X]
  dot=lambda u,v:sum(mu[x]*u[i]*v[i] for i,x in enumerate(X))
  mul=lambda B,u:[sum(a*b for a,b in zip(row,u)) for row in B]
  D=dot(g,mul(A,g));conditional=F(0)
  for Ei in Es:
   v=mul(Ei,g);conditional+=dot(g,g)-dot(v,v)
  assert D==conditional;counts['physical_conditional_dirichlet']+=1
  h=solve([[a+F(i==j) for j,a in enumerate(row)] for i,row in enumerate(A)],g)
  err=[a-b for a,b in zip(g,h)];K=dot(g,err)
  assert K==dot(err,err)+dot(h,mul(A,h))
  trial=[F((i%3)-1,3) for i in range(8)];e=[a-b for a,b in zip(g,trial)]
  assert K<=dot(e,e)+dot(trial,mul(A,trial));counts['resolvent_variational_identity']+=1
  for Ei in Es:
   v=mul(Ei,g);assert dot(g,g)-dot(v,v)<=2*K;counts['conditional_variance_resolvent']+=1
 # Literal external squared-norm failure, distinct from corrected norm inequality.
 eps=F(1,4);assert 2*eps-eps*eps>2*eps*eps and 2*eps-eps*eps<=2*eps
 counts['literal_squared_norm_counterexample']+=1
 for pairs in range(1,5):
  t=F(1,3);values=[prod(1+t*x[2*i]*x[2*i+1] for i in range(pairs)) for x in product((-1,1),repeat=2*pairs)]
  assert sum(v*v for v in values)/len(values)==(1+t*t)**pairs
  assert max(values)==(1+t)**pairs;counts['matching_density']+=1
 return dict(status='PASS',counts=dict(sorted(counts.items())),scope='Finite rational identities and geometry only; no universal mathematics, source theorem, asymptotic, contribution or acceptance certification')

if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
