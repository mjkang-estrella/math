"""Independent exact finite checks; no author code imported, no files written.
Python integers/Fractions only for exact checks; floats are separately labelled.
"""
from fractions import Fraction as Q
from itertools import product, permutations
import random, math, json
rng=random.Random(630917); count=0; cases=[]
def ck(v,label):
 global count
 count+=1
 if not v:raise AssertionError(label)
def mat(n,f=lambda i,j:0):return [[f(i,j) for j in range(n)] for i in range(n)]
def add(A,B):return [[a+b for a,b in zip(x,y)] for x,y in zip(A,B)]
def sub(A,B):return [[a-b for a,b in zip(x,y)] for x,y in zip(A,B)]
def scale(a,A):return [[a*x for x in r] for r in A]
def mul(A,B):return [[sum(a*b for a,b in zip(r,c)) for c in zip(*B)] for r in A]
def tr(A):return sum(A[i][i] for i in range(len(A)))
def dot(A,B):return sum(a*b for r,s in zip(A,B) for a,b in zip(r,s))
def norm(A):return dot(A,A)
def sums(A,n):
 out=mat(n)
 for B in A:out=add(out,B)
 return out
def comm(A,B):return sub(mul(A,B),mul(B,A))
def psd(A):
 A=[[Q(x) for x in r] for r in A];n=len(A)
 for k in range(n):
  if A[k][k]<0:return False
  if A[k][k]==0:
   if any(A[k][j]!=0 for j in range(k+1,n)):return False
  else:
   d=A[k][k]
   for i in range(k+1,n):
    for j in range(i,n):A[j][i]=A[i][j]=A[i][j]-A[i][k]*A[k][j]/d
 return True
def idx(n):return list(product(range(n),repeat=3))
def tensor(X):
 n=len(X);return {(i,j,r):X[r][i][j] for i,j,r in idx(n)}
def sym(T):return {p:sum(T[q] for q in permutations(p))/Q(6) for p in T}
def tnorm(T):return sum(x*x for x in T.values())
def tsub(T,U):return {p:T[p]-U[p] for p in T}
def slot(A,T,j):
 n=len(A);out={}
 for p in T:
  out[p]=sum(A[p[j]][a]*T[p[:j]+(a,)+p[j+1:]] for a in range(n))
 return out
def inner(T,U):return sum(T[p]*U[p] for p in T)
def swap(T):return {(i,j,k):T[i,k,j] for i,j,k in T}
def slices(T,n):return [mat(n,lambda i,j:T[i,j,r]) for r in range(n)]
def wick_tensor_quadratic(coeff):
 # E ||sum x_r x_s C_rs||^2; all three pairings, including crossing.
 n=len(coeff)
 return sum(inner(coeff[r][r],coeff[s][s])+inner(coeff[r][s],coeff[r][s])+inner(coeff[r][s],coeff[s][r]) for r in range(n) for s in range(n))
def run_family(X,label):
 n=len(X);I=mat(n,lambda i,j:int(i==j));T=tensor(X);S=tsub(T,swap(T));Y=sym(T)
 ck(3*tnorm(tsub(T,Y))==tnorm(S),label+' sym factor')
 B=sums([mul(A,A) for A in X],n);K=max(sum(abs(x) for x in r) for r in B)
 ck(psd(sub(scale(K,I),B)),label+' cap')
 crossing=sums([mul(mul(mul(A,C),A),C) for A in X for C in X],n)
 fourth=add(add(mul(B,B),sums([mul(mul(A,B),A) for A in X],n)),crossing)
 # Second implementation via Wick pairing of coefficients of L^2.
 coeff=[[mul(A,C) for C in X] for A in X]
 direct=sums([add(add(mul(coeff[r][r],coeff[s][s]),mul(coeff[r][s],coeff[r][s])),mul(coeff[r][s],coeff[s][r])) for r in range(n) for s in range(n)],n)
 ck(fourth==direct,label+' Wick expansion');ck(psd(sub(scale(3*K*K,I),fourth)),label+' operator fourth bound')
 for r,s,t,i in product(range(n),repeat=4):
  # Explicit polynomial derivative of L^2, and separate error expansion.
  z=sum((X[t][i][a]*X[r][a][s]+X[r][i][a]*X[t][a][s]-X[t][i][a]*X[s][a][r]-X[s][i][a]*X[t][a][r]) for a in range(n))
  c=comm(X[r],X[s])[i][t]
  err=sum(X[r][i][a]*S[a,s,t]-X[s][i][a]*S[a,r,t]+X[t][i][a]*S[a,s,r] for a in range(n))
  ck(z==c+err,label+' polynomial curl coefficient')
 if n<=6:
  V={p:rng.randint(-2,2) for p in T}
  for j in range(3):
   e2=sum(tnorm(slot(A,V,j)) for A in X)
   ck(e2<=K*tnorm(V),label+' fixed tensor second moment')
   for a in range(3):
    cs=[[slot(A,slot(C,V,a),j) for C in X] for A in X]
    e4=wick_tensor_quadratic(cs)
    ck(e4<=3*K*K*tnorm(V),label+' correlated slot fourth moment')
 # Channel identity on all matrix units for fully symmetric Y.
 Ys=slices(Y,n);BY=sums([mul(A,A) for A in Ys],n);distance=Q(0)
 for i,j in product(range(n),repeat=2):
  H=mat(n,lambda a,b:int((a,b)==(i,j)))
  Phi=sums([mul(mul(A,H),A) for A in Ys],n)
  PT=sums([scale(A[i][j],A) for A in Ys],n)
  distance+=norm(sub(Phi,PT))
 E=sum(norm(comm(A,C)) for A in Ys for C in Ys)
 ck(distance==E,label+' channel all matrix units')
 co=Q(0)
 for i,j,k,r in product(range(n),repeat=4):
  a=sum(Y[i,j,b]*Y[b,k,r]-Y[j,k,b]*Y[i,b,r] for b in range(n))
  ck(a==comm(Ys[i],Ys[k])[j][r],label+' coassociator ordered entry');co+=a*a
 ck(co==E,label+' coassociator norm')
 cases.append(dict(label=label,m=n))
for n in [1,2,4,6,8]:
 X=[]
 for r in range(n):
  A=mat(n)
  for i in range(n):
   for j in range(i,n):A[i][j]=A[j][i]=rng.randint(-2,2)
  X.append(A)
 run_family(X,'dense-'+str(n))
for n in [3,6,9]:
 X=[mat(n,lambda i,j:int(i==j and r==0)) for r in range(n)]
 run_family(X,'uncapped-third-'+str(n))
 ck(sum(norm(A) for A in X)==n,'third Gram eigenvalue m versus B=I')
# Explicit negative Wick crossing: three real symmetric anticommuting 4x4 matrices.
Z=[[1,0],[0,-1]];H=[[0,1],[1,0]];I2=[[1,0],[0,1]]
def kron(A,B):return [[A[i//len(B)][j//len(B)]*B[i%len(B)][j%len(B)] for j in range(len(A)*len(B))] for i in range(len(A)*len(B))]
X=[kron(Z,I2),kron(H,Z),kron(H,H)]
C=sums([mul(mul(mul(A,B),A),B) for A in X for B in X],4)
ck(C==scale(-3,mat(4,lambda i,j:int(i==j))),'negative crossing is -3I')
# Active repair cutoff in dimension >=29, plus harmless scalar blocks.
for d,extra in [(29,0),(37,0),(37,200),(113,500)]:
 n=d+extra;e2=Q(2*(d-1),3);a2=Q(d+8,9);x2=d
 sparseX={(i,i,0):Q(1) for i in range(d)}
 sparseX.update({(i,i,i):Q(1) for i in range(d,n)})
 sparseT={}
 for p,c in sparseX.items():
  for pp in permutations(p):sparseT[pp]=sparseT.get(pp,0)+c/6
 actual_e=sum((sparseT.get(p,0)-sparseX.get(p,0))**2 for p in set(sparseX)|set(sparseT))
 gram={}
 for (i,j,r),c in sparseT.items():gram[i]=gram.get(i,0)+c*c
 ck(actual_e==e2,'actual sparse symmetrization error')
 ck(gram[0]==a2 and all(gram[i]==Q(2,9) for i in range(1,d)),'actual first flattening diagonal')
 sparseZ={p:c for p,c in sparseT.items() if 0 not in p}
 ck(sparseZ=={(i,i,i):Q(1) for i in range(d,n)},'actual all-slot spectral compression')
 ck(sum((sparseZ.get(p,0)-sparseX.get(p,0))**2 for p in set(sparseX)|set(sparseZ))==x2,'actual repaired distance')
 ck(a2>4,'symmetrization really exceeds 4K');ck(a2<=4*e2,'discarded first mass')
 ck(Q(d+2,3)<=12*e2,'all-slot discarded T mass');ck(x2<=26*e2,'Z-X repair')
 ck(d<=234*e2,'repair B difference');ck(0<=936*e2,'commuting original and compressed repair')
 cases.append(dict(label='active-repair-star-with-scalar-blocks',m=n,normalized_sym_error=str(e2/n)))
# Generic partial trace CP obstruction: rational orthogonal Householder bases; all-bases proof is analytic.
for k in [2,3,4]:
 n=k*k;v=list(range(1,n+1));vv=sum(x*x for x in v)
 U=mat(n,lambda i,j:Q(int(i==j))-Q(2*v[i]*v[j],vv));overlap=Q(0)
 for j in range(n):
  u=[U[i][j] for i in range(n)]
  rho=mat(k,lambda a,b:sum(u[a*k+c]*u[b*k+c] for c in range(k)))
  ck(tr(rho)==1,'partial trace unnormalized trace one')
  purity=norm(rho);ck(purity<=1,'purity <=1');overlap+=purity/k
 ck(2*n-2*overlap>=2*n*(1-Q(1,k)),'all real Householder basis bound')
# Harmonic tensor with a=1 first; all quadratic channel quantities divide by 2 to normalize.
T={(i,j,r):(1 if (i,j,r)==(0,0,0) else -1 if sorted((i,j,r))==[0,1,1] else 0) for i,j,r in idx(2)}
X=slices(T,2);J=[[0,1],[-1,0]]
for M,eig in [(I2,1),(Z,0),(H,0),(J,-1)]:
 phi=scale(Q(1,2),sums([mul(mul(A,M),A) for A in X],2));ck(phi==scale(eig,M),'harmonic eigenvalue')
ck(sum(norm(comm(A,B)) for A in X for B in X)/4==4,'harmonic E=4')
# Exact one-step deflation identities for arbitrary symmetric cubics in adapted stationary coordinates.
for n in [3,5,7]:
 T=sym({p:Q(rng.randint(-2,2)) for p in idx(n)})
 for p in T:
  if p.count(0)==2:T[p]=0
 X=slices(T,n);Hp=[r[1:] for r in X[0][1:]];Xp=[[row[1:] for row in A[1:]] for A in X[1:]]
 B=sums([mul(A,A) for A in X],n)
 ck([row[1:] for row in B[1:]]==add(sums([mul(A,A) for A in Xp],n-1),scale(2,mul(Hp,Hp))),'deflation B')
 c=T[0,0,0];assoc=Q(0)
 for j in range(1,n):
  w=[comm(X[0],X[j])[i][0] for i in range(n)];assoc+=sum(x*x for x in w)
 ck(assoc==norm(sub(mul(Hp,Hp),scale(c,Hp))),'contracted adaptive identity')
 for j,k in product(range(n-1),repeat=2):
  correction=mat(n-1,lambda a,b:Hp[a][j]*Hp[b][k]-Hp[a][k]*Hp[b][j])
  ck(comm(Xp[j],Xp[k])==sub([r[1:] for r in comm(X[j+1],X[k+1])[1:]],correction),'deflation commutators')
# Full tensor rotation of a polynomial Frechet derivative, including the derivative index.
for n in [3,5]:
 X=[]
 for r in range(n):
  A=mat(n)
  for i in range(n):
   for j in range(i,n):A[i][j]=A[j][i]=rng.randint(-1,1)
  X.append(A)
 T=tensor(X);v=list(range(1,n+1));vv=sum(a*a for a in v)
 U=mat(n,lambda i,j:Q(int(i==j))-Q(2*v[i]*v[j],vv))
 rot=lambda V:slot(U,slot(U,slot(U,V,0),1),2)
 TT=rot(T);XX=slices(TT,n);x=[Q(i-1,3) for i in range(n)];y=[sum(U[i][j]*x[j] for j in range(n)) for i in range(n)]
 def pcurl(X,x):
  L=sums([scale(a,A) for a,A in zip(x,X)],len(X))
  d=[add(scale(Q(1,2),A),scale(Q(1,10),add(mul(L,A),mul(A,L)))) for A in X]
  V=tensor(d);return tsub(V,swap(V))
 ck(rot(pcurl(X,x))==pcurl(XX,y),'all three derivative tensor indices rotate')
 ck(tnorm(rot(T))==tnorm(T),'rational tensor rotation preserves norm')
# Exact paired estimates for a strictly convex polynomial on [-1,1].
ar=Q(3,10);hr=Q(1,5);MR=16/ar**2+16/hr**2*(1+2/ar**2)
grid=[Q(-1),Q(-1,2),Q(0),Q(1,2),Q(1)]
for i,s,r in product(grid,repeat=3):
 alpha=Q(1,2)+(i+s)/10;beta=Q(1,2)+(i+r)/10
 gamma=Q(1,2)-(i+s)/10;eta=Q(1,2)-(i+r)/10
 ck((alpha-beta)*(gamma-eta)<=0,'reflected divided differences opposite')
 for A,C in product(range(-2,3),repeat=2):
  ep=alpha*A-beta*C;em=gamma*A-eta*C;w=ep*ep+em*em
  ck((A-C)**2<=2/ar**2*w,'exact paired symmetry degeneracies')
  ck(((i+s)*A-(i+r)*C)**2<=MR*w,'exact paired polynomial curl degeneracies')
# Independent sparse Hermite Hodge checks in higher degrees than the author suite.
def pn(p):return sum(c*c*math.prod(math.factorial(a) for a in e) for e,c in p.items())
def plus(p,q,sgn=1):
 out=dict(p)
 for e,c in q.items():out[e]=out.get(e,0)+sgn*c
 return out
def deriv(p,j,adj=False):
 out={}
 for e,c in p.items():
  if adj or e[j]:
   a=list(e);a[j]+=1 if adj else -1;a=tuple(a)
   out[a]=out.get(a,0)+c*(1 if adj else e[j])
 return out
for n,k in product([1,3,6,8],[0,1,2,7,9]):
 V=[{} for _ in range(n)]
 for _ in range(30):
  e=[0]*n
  for j in range(k):e[rng.randrange(n)]+=1
  j=rng.randrange(n);e=tuple(e);V[j][e]=V[j].get(e,0)+rng.randint(-3,3)
 div={}
 for j in range(n):div=plus(div,deriv(V[j],j,True))
 curl=sum(pn(plus(deriv(V[s],r),deriv(V[r],s),-1)) for r in range(n) for s in range(r+1,n))
 ck(curl==(k+1)*sum(pn(v) for v in V)-pn(div),'Hermite degree Hodge identity')
 residual=sum(pn(plus(V[j],{e:Q(c,k+1) for e,c in deriv(div,j).items()},-1)) for j in range(n))
 ck(residual==Q(curl,k+1),'resolvent N+2 rather than N+1')
# Floating Mills checks include negative and positive tails, repeated eigenvalues and zero gap.
def q(x):return math.exp(-x*x/2)/math.sqrt(2*math.pi)/(math.erfc(x/math.sqrt(2))/2)
def qp(x):v=q(x);return v*(v-x)
def qpp(x):v=q(x);d=v-x;return v*(d*d+v*d-1)
def dd(a,b):return qp(a) if a==b else (q(a)-q(b))/(a-b)
floats=[]
for a in [-20,-12,-7,-2,0,2,7,12,20]:
 v=qpp(a);floats.append(dict(kind='scalar',x=a,q2=v,positive=v>0))
for R in [1,2,5,10]:
 ar=R*math.exp(-R*R/2)/math.sqrt(2*math.pi);hr=R/(2*math.pi)*math.exp(-R*R-4*R-20)
 for l in [(-R,0,R),(R,R,R),(-R,R,R),(0,0,0),(R,-R,0)]:
  i,s,r=l;A=Q(7,3);C=Q(-5,2);ep=dd(i,s)*float(A)-dd(i,r)*float(C);em=dd(-i,-s)*float(A)-dd(-i,-r)*float(C)
  d=float(A-C);z=(i+s)*float(A)-(i+r)*float(C);M=16*R*R/ar**2+16/hr**2*(1+2/ar**2)
  floats.append(dict(kind='paired',R=R,eigenvalues=l,d_inequality=d*d<=2/ar**2*(ep*ep+em*em),z_inequality=z*z<=M*(ep*ep+em*em)))
print(json.dumps(dict(status='PASS',exact_assertions=count,cases=cases,floating_records=floats,limitation='Finite diagnostics only. Floating positivity and inequalities are not analytic certificates; no author code imported.'),indent=2,sort_keys=True))
