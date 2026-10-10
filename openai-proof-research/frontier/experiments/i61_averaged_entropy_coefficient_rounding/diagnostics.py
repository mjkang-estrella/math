"""Read-only, standard-library finite checks. No analytic certification."""
from fractions import Fraction as F
from itertools import product, permutations
import math, random, json
count=0
cases={}
def check(v,label):
 global count
 count+=1
 if not v: raise AssertionError(label)
 cases[label]=cases.get(label,0)+1
def zero(n):return [[F(0) for _ in range(n)] for _ in range(n)]
def ident(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def add(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def sub(a,b):return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(a,c):return [[c*x for x in r] for r in a]
def mm(a,b):return [[sum(x*y for x,y in zip(r,c)) for c in zip(*b)] for r in a]
def tr(a):return sum(a[i][i] for i in range(len(a)))
def dot(a,b):return sum(x*y for r,s in zip(a,b) for x,y in zip(r,s))
def ns(a):return dot(a,a)
def vs(a):return sum(x*x for x in a)
def vadd(a,b):return [x+y for x,y in zip(a,b)]
def msum(a,n):
 z=zero(n)
 for b in a:z=add(z,b)
 return z
def comm(a,b):return sub(mm(a,b),mm(b,a))
def det(a):
 if len(a)==0:return F(1)
 if len(a)==1:return a[0][0]
 return sum((-1)**j*a[0][j]*det([r[:j]+r[j+1:] for r in a[1:]]) for j in range(len(a)))
def psd(a):
 n=len(a)
 return all(det([[a[i][j] for j in ids] for i in ids])>=0 for mask in range(1,1<<n) for ids in [[i for i in range(n) if mask>>i&1]])
def tensor(x):
 n=len(x);return {(i,j,r):x[r][i][j] for i,j,r in product(range(n),repeat=3)}
def slices(t,n):return [[[t[i,j,r] for j in range(n)] for i in range(n)] for r in range(n)]
def tdot(a,b):return sum(a[k]*b[k] for k in a)
def tsub(a,b):return {k:a[k]-b[k] for k in a}
def tadd(a,b):return {k:a[k]+b[k] for k in a}
def sym(t):return {k:sum(t[p] for p in permutations(k))/6 for k in t}
def slot(a,t,j,n):
 return {k:sum(a[k[j]][b]*t[k[:j]+(b,)+k[j+1:]] for b in range(n)) for k in t}
def momentquad(v,n):
 d={k:sum(v[r,r][k] for r in range(n)) for k in v[0,0]}
 return tdot(d,d)+sum(tdot(v[r,s],tadd(v[r,s],v[s,r])) for r,s in product(range(n),repeat=2))
rng=random.Random(61059)
for n in range(1,5):
 for rep in range(4):
  x=[]
  for r in range(n):
   a=zero(n)
   for i in range(n):
    for j in range(i,n):a[i][j]=a[j][i]=F(rng.randrange(-3,4),7*n)
   x.append(a)
  T=tensor(x); W=sym(T); S={k:T[k]-T[k[0],k[2],k[1]] for k in T}
  check(tdot(S,S)==3*tdot(tsub(T,W),tsub(T,W)),'symmetrization factor three')
  B=msum([mm(a,a) for a in x],n)
  K=max(sum(abs(v) for v in row) for row in B)
  check(psd(sub(scale(ident(n),K),B)),'row-sum operator cap')
  fourth=zero(n)
  for a,b in product(x,repeat=2):
   fourth=add(fourth,add(add(mm(mm(a,a),mm(b,b)),mm(mm(a,b),mm(a,b))),mm(mm(a,b),mm(b,a))))
  rhs=add(add(mm(B,B),msum([mm(mm(a,B),a) for a in x],n)),msum([mm(mm(a,b),mm(a,b)) for a,b in product(x,repeat=2)],n))
  check(fourth==rhs,'Wick fourth moment identity')
  check(psd(sub(scale(ident(n),3*K*K),fourth)),'fourth operator moment bound')
  for j,a in product(range(3),repeat=2):
   v={(r,s):slot(x[r],slot(x[s],T,a,n),j,n) for r,s in product(range(n),repeat=2)}
   check(momentquad(v,n)<=3*K*K*tdot(T,T),'tensor-slot fourth moment all pairs')
  polynomial_energy=F(0);error_energy=F(0);comm_energy=F(0)
  for r,s in product(range(n),repeat=2):
   cm=comm(x[r],x[s]);comm_energy+=ns(cm)
   for t in range(n):
    for i in range(n):
     z=(add(mm(x[r],x[t]),mm(x[t],x[r])))[i][s]-(add(mm(x[s],x[t]),mm(x[t],x[s])))[i][r]
     err=sum(x[r][i][a]*(x[t][a][s]-x[s][a][t])-x[s][i][a]*(x[t][a][r]-x[r][a][t])+x[t][i][a]*(x[r][a][s]-x[s][a][r]) for a in range(n))
     check(z==cm[i][t]+err,'exact polynomial curl coefficient')
     polynomial_energy+=z*z;error_energy+=err*err
  check(error_energy<=9*K*tdot(S,S),'family error without matrix-count factor')
  check(comm_energy<=2*polynomial_energy+18*K*tdot(S,S),'coefficient commutator bound')
  # Channel and coassociator on independent fully symmetric arrays, B need not be I.
  y=slices(W,n);BB=msum([mm(a,a) for a in y],n)
  for r,s in product(range(n),repeat=2):check(dot(y[r],y[s])==BB[r][s],'linked slice Gram equals B')
  cd=sum(ns(comm(a,b)) for a,b in product(y,repeat=2));hs=F(0);assoc=F(0)
  for a,b in product(range(n),repeat=2):
   E=zero(n);E[a][b]=F(1)
   ph=msum([mm(mm(v,E),v) for v in y],n)
   pr=msum([scale(v,dot(v,E)) for v in y],n)
   hs+=ns(sub(ph,pr))
  for i,j,k,r in product(range(n),repeat=4):
   aa=sum(W[i,j,a]*W[a,k,r]-W[j,k,a]*W[i,a,r] for a in range(n))
   check(aa==comm(y[i],y[k])[j][r],'coassociator entries')
   assoc+=aa*aa
  check(hs==cd==assoc,'channel coassociator norm identity')
# Rational paired-difference model f(x)=x/2+x^2/8, satisfying all local assumptions on [-1,1].
grid=[F(-1),F(-1,2),F(0),F(1,2),F(1)]
a0=F(1,4);h0=F(1,4);M=16/a0**2+16/h0**2*(1+2/a0**2)
def divided(a,b):return F(1,2)+(a+b)/8
for a,b,c in product(grid,repeat=3):
 for A,C in [(F(2,3),F(-4,5)),(F(1),F(1)),(F(-1,7),F(3,4))]:
  e=divided(a,b)*A-divided(a,c)*C;f=divided(-a,-b)*A-divided(-a,-c)*C;ee=e*e+f*f
  check((A-C)**2<=2/a0**2*ee,'paired cancellation exact scalar model')
  check(((b-c)*C)**2<=8/h0**2*(1+2/a0**2)*ee,'paired gap exact scalar model')
  check(((a+b)*A-(a+c)*C)**2<=M*ee,'paired polynomial curl exact scalar model')
# Explicit rational Kraus channel for harmonic tensor, bypass irrational entries by scaling.
Z=[[F(1),F(0)],[F(0),F(-1)]];X=[[F(0),F(-1)],[F(-1),F(0)]]
J=[[F(0),F(1)],[F(-1),F(0)]]
def harmonic_phi(a):return scale(add(mm(mm(Z,a),Z),mm(mm(X,a),X)),F(1,2))
for a,v in [(ident(2),1),(Z,0),(X,0),(J,-1)]:check(harmonic_phi(a)==scale(a,v),'harmonic channel eigenvalue')
check(sub(harmonic_phi(harmonic_phi(J)),harmonic_phi(J))==scale(J,2),'cb norm lower obstruction')
check(ns(comm(Z,X))/2==4,'harmonic normalized commutator energy')
# Conditional expectation rank and overlap in dimensions k^2, all matrix units.
for k in [2,3]:
 n=k*k
 def expect(a):
  b=[[sum(a[i*k+l][j*k+l] for l in range(k))/k for j in range(k)] for i in range(k)]
  return [[b[i//k][j//k]*F(i%k==j%k) for j in range(n)] for i in range(n)]
 hsnorm=F(0);overlap=F(0)
 for i,j in product(range(n),repeat=2):
  e=zero(n);e[i][j]=F(1);z=expect(e)
  check(expect(z)==z,'conditional expectation exact idempotence')
  hsnorm+=ns(z)
  if i==j:overlap+=ns(z)
 check(hsnorm==n,'conditional expectation rank m')
 check(overlap==F(n,k),'product-basis overlap attains universal upper bound')
 check((2*n-2*overlap)/n==2*(1-F(1,k)),'dephasing lower-bound formula')
for d in range(2,101):
 u=F(1,d);Q=F(43,100)+F(26,100)*(u-F(1,2))+F(68,25)*(u-F(1,2))**2
 check(1-u-Q-F(7,50)*u==F(1,50)*(1-2*u)*(1+68*u),'inherited simultaneous chaos surplus')
 check(F(1,500)+F((d-2)*(d+68),50*d)>=F(d,1000),'inherited Sobolev coefficient')
# Floating evaluations: scalar Mills values only, explicitly not certified minima/upper bounds.
def q(a):return math.sqrt(2/math.pi)*math.exp(-a*a/2)/math.erfc(a/math.sqrt(2))
def qp(a):return q(a)*(q(a)-a)
def qpp(a):
 z=q(a);d=z-a;return z*(d*d+z*d-1)
def dd(a,b):return (q(a)-q(b))/(a-b) if abs(a-b)>1e-7 else qp((a+b)/2)
floats=[]
for R in [1.,2.,3.,4.,6.]:
 lower1=R*math.exp(-R*R/2)/math.sqrt(2*math.pi)
 lower2=R/(2*math.pi)*math.exp(-R*R-4*R-20)
 vals=[-R+2*R*i/100 for i in range(101)]
 floats.append(dict(kind='uncertified scalar sample minima',R=R,sampled_qprime_min=min(qp(v) for v in vals),sampled_qsecond_min=min(qpp(v) for v in vals),analytic_lower_a_float=lower1,analytic_lower_h_float=lower2))
for a,b,c in [(-2.,-1.,1.),(2.,1.,-1.),(0.,1.,1.),(-6.,-5.,-4.),(6.,5.,4.)]:
 A,C=.7,-.4
 ep=dd(a,b)*A-dd(a,c)*C;em=dd(-a,-b)*A-dd(-a,-c)*C
 floats.append(dict(kind='uncertified paired Mills evaluation',eigenvalues=[a,b,c],A=A,C=C,eplus=ep,eminus=em,polynomial_curl=(a+b)*A-(a+c)*C))
print(json.dumps(dict(status='PASS',exact_assertions=count,exact_groups=cases,floating_records=floats,scope='Finite rational identities and labeled scalar floating evaluations only; no universal proof or independent analytic acceptance.'),sort_keys=True,indent=2))
