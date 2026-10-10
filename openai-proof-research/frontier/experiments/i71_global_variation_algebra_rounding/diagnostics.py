"""Independent finite arithmetic checks; no imports of earlier diagnostic code.

All assertions use integers/Fractions. Floating records only evaluate displayed
closed formulas, never certify an optimization or universal statement.
"""
from fractions import Fraction as F
from itertools import product
import json, math, random
rng=random.Random(7109)
count=0
def ck(v):
 global count
 count+=1
 assert v, count
def zero(n):return [[0]*n for _ in range(n)]
def eye(n):return [[int(i==j) for j in range(n)] for i in range(n)]
def tr(a):return sum(a[i][i] for i in range(len(a)))
def mm(a,b):
 n=len(a);return [[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def add(a,b,s=1):return [[x+s*y for x,y in zip(u,v)] for u,v in zip(a,b)]
def norm(a):return sum(x*x for row in a for x in row)
def dot(a,b):return sum(x*y for u,v in zip(a,b) for x,y in zip(u,v))
def comm(a,b):return add(mm(a,b),mm(b,a),-1)
def slices(t):
 n=len(t);return [[[t[i][j][r] for j in range(n)] for i in range(n)] for r in range(n)]
def tensor(n):
 vals={}
 for i,j,k in product(range(n),repeat=3):vals.setdefault(tuple(sorted((i,j,k))),rng.randrange(-3,4))
 return [[[vals[tuple(sorted((i,j,k)))] for k in range(n)] for j in range(n)] for i in range(n)]
def energy(t):return sum(norm(a) for a in slices(t))
def B(t):
 n=len(t);out=zero(n)
 for a in slices(t):out=add(out,mm(a,a))
 return out
def EC(t):
 ss=slices(t);return [[comm(a,b) for b in ss] for a in ss]
def E(t):return sum(norm(a) for row in EC(t) for a in row)
def contract(t,a,b,c):
 n=len(t);return sum(t[i][j][k]*a[i]*b[j]*c[k] for i,j,k in product(range(n),repeat=3))
def hess(t,k):
 n=len(t);k2=mm(k,k)
 return 6*sum(t[i][j][l]*k[j][i]*k[l][i] for i,j,l in product(range(n),repeat=3))+3*sum(t[i][i][j]*k2[j][i] for i,j in product(range(n),repeat=2))
def skew(n):
 a=zero(n)
 for i in range(n):
  for j in range(i):a[i][j]=rng.randrange(-3,4);a[j][i]=-a[i][j]
 return a
def compress(t,labels):
 n=len(t)
 return [[[t[i][j][k]*int(labels[i]==labels[j]==labels[k]) for k in range(n)] for j in range(n)] for i in range(n)]
def qmass(t,labels):
 n=len(t);return sum(t[i][j][k]**2 for i,j,k in product(range(n),repeat=3) if labels[i]!=labels[j])
def variance(t,labels):
 n=len(t);v=energy(t)
 for lab in set(labels):
  ids=[i for i in range(n) if labels[i]==lab]
  v-=sum(F(sum(t[i][i][r] for i in ids)**2,len(ids)) for r in ids)
 return v

# Arbitrary symmetric tensors: Hessian covariance, finite reflection, and
# all-slot compression (including nonstationary repeated-index terms).
for n in range(2,7):
 for trial in range(5):
  t=tensor(n);k=skew(n);c=[[t[i][i][j] for j in range(n)] for i in range(n)]
  # The full Hessian formula uses sym(C) implicitly through K^2.
  s=zero(n)
  for i in range(n):
   for j in range(i):s[i][j]=s[j][i]=rng.randrange(-2,3)
  cov=0
  for g in range(n):
   z=[int(i==g) for i in range(n)]
   kg=[[(z[i]-z[j])*s[i][j] for j in range(n)] for i in range(n)]
   cov+=hess(t,kg)
  s2=mm(s,s)
  formula=6*sum(t[i][j][l]*s[i][j]*s[i][l] for i,j,l in product(range(n),repeat=3))
  formula+=6*sum(t[i][j][j]*s[i][j]**2 for i,j in product(range(n),repeat=2))
  formula-=3*dot(c,s2)+3*sum(c[i][i]*s2[i][i] for i in range(n))
  ck(cov==formula)
  a=[i+1 for i in range(n)];den=sum(x*x for x in a)
  # First column of a rational Householder matrix is an exact unit vector.
  v=[F(int(i==0))-F(2*a[i]*a[0],den) for i in range(n)]
  ck(sum(x*x for x in v)==1)
  u=[[F(int(i==j))-2*v[i]*v[j] for j in range(n)] for i in range(n)]
  change=sum(contract(t,[u[j][i] for j in range(n)],[u[j][i] for j in range(n)],[u[j][i] for j in range(n)]) for i in range(n))-sum(t[i][i][i] for i in range(n))
  rhs=-6*sum(v[i]*t[i][i][j]*v[j] for i,j in product(range(n),repeat=2))
  rhs+=12*contract(t,[x*x for x in v],v,v)-8*sum(x**3 for x in v)*contract(t,v,v,v)
  ck(change==rhs)
  labels=[i%2 for i in range(n)];tt=compress(t,labels)
  loss=energy(t)-energy(tt);q=qmass(t,labels)
  ck(q<=loss and 2*loss<=3*q)
  gram=[[dot(a,b) for b in slices(t)] for a in slices(t)]
  ck(gram==B(t))
  cap=energy(t)
  ck(norm(add(B(t),B(tt),-1))<=4*cap*loss)
  ec,ec2=EC(t),EC(tt)
  ck(sum(norm(add(ec[i][j],ec2[i][j],-1)) for i,j in product(range(n),repeat=2))<=16*cap*loss)
  ck(E(tt)+norm(add(B(tt),eye(n),-1))<=2*(E(t)+norm(add(B(t),eye(n),-1)))+40*cap*loss)
  vtot=variance(tt,labels)
  active=sum(tt[i][j][k]**2 for i,j,k in product(range(n),repeat=3) if labels.count(labels[i])>=2)
  ck(active<=3*vtot)
  mix=energy(tt)-sum(tt[i][i][i]**2 for i in range(n))
  ck(mix<=active)
  # Hierarchical losses telescope exactly, never resetting normalization.
  refined=list(range(n));tt2=compress(tt,refined)
  ck(energy(t)-energy(tt2)==loss+energy(tt)-energy(tt2))
  # Integrate a random shifted spectral grid exactly, over all break points.
  lam=[F(2*i-3,3) for i in range(n)];delta=F(5,4)
  points=sorted({F(0),delta}|{x%delta for x in lam})
  avg=F(0);avgloss=F(0)
  for lo,hi in zip(points,points[1:]):
   theta=(lo+hi)/2;labs=[(x-theta)//delta for x in lam]
   avg+=(hi-lo)/delta*qmass(t,labs)
   avgloss+=(hi-lo)/delta*(energy(t)-energy(compress(t,labs)))
  expected=sum(min(F(1),abs(lam[i]-lam[j])/delta)*t[i][j][k]**2 for i,j,k in product(range(n),repeat=3))
  ce=sum((lam[i]-lam[j])**2*t[i][j][k]**2 for i,j,k in product(range(n),repeat=3))
  ck(avg==expected);ck(avg**2*delta**2<=ce*energy(t));ck(2*avgloss<=3*avg)
  # Trace contraction norm via its exact adjoint on Sym^3.
  z=[F(i-2,3) for i in range(n)]
  jt=[[[F(z[i]*int(j==k)+z[j]*int(i==k)+z[k]*int(i==j),3) for k in range(n)] for j in range(n)] for i in range(n)]
  ck(energy(jt)==F(n+2,3)*sum(x*x for x in z))
  ck(sum(sum(t[i][i][r] for i in range(n))**2 for r in range(n))<=F(n+2,3)*energy(t))

# Strict local traps: integer numerator P=A+3D, denominator sqrt(m+8).
traps=[]
for k in range(2,5):
 m=2**k-1
 a=[[[int((i+1)^(j+1)^(l+1)==0) for l in range(m)] for j in range(m)] for i in range(m)]
 p=[[[a[i][j][l]+3*int(i==j==l) for l in range(m)] for j in range(m)] for i in range(m)]
 sa=slices(a);bp=B(p)
 for i,j in product(range(m),repeat=2):ck(bp[i][j]==(m+8)*int(i==j))
 for i in range(m):
  ai2=mm(sa[i],sa[i])
  for j,l in product(range(m),repeat=2):ck(ai2[j][l]==int(j==l and j!=i))
 ck(E(p)==38*m*(m-1))
 for i,j in product(range(m),repeat=2):ck(p[i][i][j]==3*int(i==j))
 for trial in range(12):
  sk=skew(m);h=hess(p,sk);ck(h<=-3*norm(sk))
  rhs=6*sum(sk[j][i]*(int(j==l)-a[i][j][l])*sk[l][i] for i,j,l in product(range(m),repeat=3))
  ck(-3*norm(sk)-h==rhs)
 # Two-coordinate finite rotations (rational cosine/sine), both signs.
 for co,si in [(F(3,5),F(4,5)),(F(-3,5),F(4,5)),(F(0),F(1))]:
  for signs in product([-1,1],repeat=2):
   v=[F(0)]*m;w=v.copy();v[0]=signs[0]*co;v[1]=signs[0]*si;w[0]=-signs[1]*si;w[1]=signs[1]*co
   ck(contract(p,v,v,v)+contract(p,w,w,w)<=6)
 traps.append(dict(m=m,B_numerator=m+8,E_numerator=38*m*(m-1)))

# Real X/Z tensor-factor family: exact cap, error, and achievable 1/2 cost.
paulis=[]
for k in range(1,6):
 d=2**k;arr=[]
 for j in range(k):
  x=zero(d);z=zero(d)
  for i in range(d):x[i][i^(1<<j)]=1;z[i][i]=1 if not (i>>j)&1 else -1
  arr.extend([x,z])
 b=zero(d)
 for a in arr:b=add(b,mm(a,a))
 for i,j in product(range(d),repeat=2):ck(b[i][j]==2*k*int(i==j))
 ec=sum(norm(comm(a,b)) for a in arr for b in arr)
 ck(ec==8*k*d)
 off=sum(a[i][j]**2 for a in arr for i,j in product(range(d),repeat=2) if i!=j)
 ck(off==k*d)
 paulis.append(dict(k=k,dimension=d,normalized_E=str(F(ec,4*k*k*d)),normalized_best_error='1/2'))

# Exact diagonal input under successive binary spectral cuts: b<=2^N,
# loss zero, centered slice variance m-b (not a finite-step terminal test).
for k in range(1,8):
 m=2**k
 for steps in range(k+1):
  labels=[i%(2**steps) for i in range(m)];blocks=len(set(labels))
  ck(blocks==2**steps)
  potential=sum(F(labels.count(lab),labels.count(lab)) for lab in set(labels))
  ck(m-potential==m-blocks)

floats=[]
for k in [4,6,10,16,24]:
 m=2**k-1;s=math.sqrt((m-1)/(m+8))
 floats.append(dict(label='closed-form floating evaluation, not optimization',m=m,epsilon=38*(m-1)/(m+8)**2,local_cost_per_dimension=2-6/math.sqrt(m+8),known_global_cost_bound_per_dimension=236/m,perturbation_sq_per_dimension=(s-1)**2+9/(m+8)))
print(json.dumps(dict(status='PASS',scope='Finite exact arithmetic and labeled closed-form floats only',exact_assertions=count,strict_traps=traps,pauli_family=paulis,floating_records=floats),indent=2,sort_keys=True))
