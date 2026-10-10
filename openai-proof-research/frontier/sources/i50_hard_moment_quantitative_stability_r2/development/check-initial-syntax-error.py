#!/usr/bin/env python3
"""Independent exact interface diagnostics; not a proof of compactness or BV."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,itertools,functools
R=Path(__file__).resolve().parents[3]
for p in sorted((R/'frontier/sources/i49_hard_moment_quantitative_stability/vendor').glob('*.whl')):sys.path.insert(0,str(p))
import sympy as s
N=0
def ck(v,label):
 global N
 assert bool(v),label
 N+=1
def eq(a,b,label):ck(s.simplify(s.expand(a-b))==0,label)
def mat_eq(a,b,label):
 for i in range(a.rows):
  for j in range(a.cols):eq(a[i,j],b[i,j],f'{label} {i},{j}')
x=s.Matrix(s.symbols('x0:3'));n=3
psi=[(x[0]+x[1])**2/2,(x[0]-x[1])**2/4,x[2]**2/2]
eps=s.Integer(1);q=2;V=eps*(x.dot(x))/2+sum(psi);M=s.hessian(V,x);tau=M.inv()
@functools.lru_cache(None)
def moment(p):
 if sum(p)==0:return s.Integer(1)
 if sum(p)%2:return s.Integer(0)
 i=next(i for i,a in enumerate(p) if a);a=list(p);a[i]-=1;out=0
 for j in range(n):
  if a[j]:
   b=a.copy();b[j]-=1;out+=a[j]*tau[i,j]*moment(tuple(b))
 return out
def E(f):return s.factor(sum(c*moment(p) for p,c in s.Poly(s.expand(f),*x).terms()))
v=x[0]**2*x[2]**2+x[0]*x[1]**3/7+x[1]**2*x[2]**2/3
P=tau*s.hessian(v,x);B=P*tau
W=s.simplify(B*M*x-s.Matrix([sum(s.diff(B[i,j],x[j]) for j in range(n)) for i in range(n)]))
K=[[[s.expand(sum(s.diff(P[a,k],x[j])*tau[j,l] for j in range(n))) for l in range(n)] for k in range(n)] for a in range(n)]
W2=P*x-s.Matrix([sum(K[a][k][k] for k in range(n)) for a in range(n)])
mat_eq(W,W2,'two coordinate row adjunctions')
DzW=W.jacobian(x)*tau;RR=DzW-B
mat_eq(DzW,DzW.T,'gradient in source');mat_eq(B,B.T,'compatible P tau')
u=(M*x).dot(W)-sum(s.diff(W[i],x[i]) for i in range(n));eq(E(u),0,'centered u')
for g in [x[0]**2,x[0]*x[2],x[0]**2*x[1]**2,x[0]*x[1]*x[2]**2,1+x[2]**4]:
 eq(E(u*g),E(W.dot(s.Matrix([s.diff(g,xx) for xx in x]))),'Gaussian adjunction')
beta=[-2,3,5];F=sum(bb*pp for bb,pp in zip(beta,psi));m=E(F);U=F-m
D=sum(bb**2*E(pp) for bb,pp in zip(beta,psi))-E(U**2)
Tenergy=E(s.trace(W.jacobian(x)**2)-s.trace(M*B*M*B))
renergy=E(s.trace(M*RR*M*RR))
derivative=sum(M[a,b]*tau[k,r]*M[l,t]*K[a][k][l]*K[b][r][t] for a,b,k,r,l,t in itertools.product(range(n),repeat=6))
denergy=E(derivative)
eq(Tenergy,renergy+2*denergy,'Gaussian retained R and full tensor energy')
regularizer=eps*E(s.trace(M*B*B)+W.dot(W));slabs=0
for bb,pp in zip(beta,psi):
 Hi=s.hessian(pp,x);gam=s.Rational(bb,q);C=B-gam*tau;Y=W-gam*x
 slabs+=E(s.trace(M*C*Hi*C)+Y.dot(Hi*Y))
eq(D+E((u-U)**2),Tenergy+regularizer+slabs,'full signed score completion')
ck(m!=0,'nonzero score mean retained');ck(renergy>0 and denergy>0,'genuine positive energies')
ck(E(s.trace(W.jacobian(x).T*W.jacobian(x)))!=E(s.trace(W.jacobian(x)**2)),'HS replacement negative control')
# Invariant contraction for arbitrary oblique constant dual map, all indices retained.
T=s.Matrix([[1,s.Rational(1,2),0],[0,2,s.Rational(1,3)],[s.Rational(1,5),0,1]]);Ti=T.inv()
pt={x[0]:s.Rational(-1,2),x[1]:s.Rational(2,3),x[2]:s.Rational(3,4)}
k0=[[[K[a][k][l].subs(pt) for l in range(n)] for k in range(n)] for a in range(n)]
kp=[[[sum(T[a,i]*Ti[j,k]*T[l,h]*k0[i][j][h] for i,j,h in itertools.product(range(n),repeat=3)) for l in range(n)] for k in range(n)] for a in range(n)]
tp=T*tau*T.T;mp=tp.inv()
def contract(k,t,m):return s.factor(sum(m[a,b]*t[c,d]*m[e,f]*k[a][c][e]*k[b][d][f] for a,b,c,d,e,f in itertools.product(range(n),repeat=6)))
eq(contract(k0,tau,M),contract(kp,tp,mp),'oblique six-index covariance')
r0=RR.subs(pt);rp=T*r0*T.T
eq(s.trace(M*r0*M*r0),s.trace(mp*rp*mp*rp),'oblique retained square covariance')
# Fully symmetric S and only last-two-symmetric J, independently constructed.
I=list(itertools.product(range(n),repeat=3));J={p:s.Rational(1+2*p[0]+min(p[1:])+3*max(p[1:]),7) for p in I};S={p:s.Rational(1+sum(p)+s.prod(i+1 for i in p),11) for p in I}
k={p:S[p]+J[p[1],p[0],p[2]] for p in I}
def sym(a,p):return sum(a[t] for t in itertools.permutations(p))/6
lhs=sum(2*(S[p]+sym(J,p))**2+(J[p]-J[p[1],p[0],p[2]])**2/6 for p in I)
rhs=sum(k[p]**2/2+s.Rational(3,2)*sym(k,p)**2 for p in I)
eq(lhs,rhs,'retained tensor identity for all components')
# Radial area formula on an actual facet of box [-1,1]x[-2,2]x[-3,3].
theta=s.Matrix([s.Rational(2,3),s.Rational(1,3),s.Rational(2,3)]);v1=s.Matrix([s.Rational(2,3),s.Rational(-2,3),s.Rational(-1,3)]);v2=theta.cross(v1);p=theta[0];gp=s.Matrix([1,0,0])
a=v1/p-theta*(gp.dot(v1))/p**2;b=v2/p-theta*(gp.dot(v2))/p**2
jac=s.sqrt(a.cross(b).dot(a.cross(b)))
eq(jac,p**(-n)*s.sqrt(gp.dot(gp)),'full homogeneous radial Jacobian')
ck(jac!=p**(-n)*s.sqrt((gp-p*theta).dot(gp-p*theta)),'spherical-gradient Jacobian negative control')
# Transverse averaging on a full cube, not restrictions of Hessians to lines.
z=s.symbols('z0:3');eta=s.symbols('eta',positive=True);phi=sum(t*t for t in z)/2+eta*sum(z)**4/24
G=s.Matrix([s.diff(phi,t) for t in z]);Fav=[]
for i in range(n):
 f=G[i]
 for j in range(n):
  if i!=j:f=s.integrate(f,(z[j],-1,1))/2
 Fav.append(s.expand(f));eq(f.subs(z[i],-z[i]),-f,'odd transverse gradient')
err=sum((G[i]-Fav[i])**2 for i in range(n))
for zz in z:err=s.integrate(err,(zz,-1,1))
err=s.factor(err);ck(err>0,'positive full cube average error')
for i in range(n):ck(s.diff(Fav[i],z[i]).subs(z[i],0)>0,'factor gradient monotone at zero')
# Block area scaling and mixed-volume orientation from rectangular volume polynomial.
a=s.Matrix([1,2,3]);b=s.Matrix([s.Rational(3,2),s.Rational(5,3),s.Rational(7,2)]);h=s.symbols('h')
vola=8*s.prod(a);volb=8*s.prod(b);mixed=s.diff(8*s.prod(a[i]+h*b[i] for i in range(n)),h).subs(h,0)/3
surface_integral=sum(8*s.prod(a[j] for j in range(n) if j!=i)*b[i] for i in range(n))
eq(surface_integral,3*mixed,'anisotropic perimeter orientation')
ck(mixed!=volb*sum(a[i]/b[i] for i in range(n))/3,'orientation is not symmetric in dimension three')
Tblock=s.diag(2,2,3);normal=s.Matrix([s.Rational(3,5),s.Rational(4,5),0]);tang1=s.Matrix([s.Rational(-4,5),s.Rational(3,5),0]);tang2=s.Matrix([0,0,1]);cp=(Tblock*tang1).cross(Tblock*tang2)
eq(s.sqrt(cp.dot(cp)),Tblock.det()/2,'multidimensional block tangential Jacobian')
# Hard Neumann diagnostic and actual small-support perturbation bound.
kappa=s.symbols('kappa',nonzero=True,real=True);un=-kappa*x[0]*x[1]/2;wn=s.Matrix([s.diff(un,t) for t in x]);eq(sum(s.diff(wn[i],x[i]) for i in range(n)),0,'harmonic Neumann potential');eq(wn.dot(x),-kappa*x[0]*x[1],'ball normal flux')
rad=s.diag(3,2,2);dw=wn.jacobian(x)*rad;ck(s.simplify(dw[0,1]-dw[1,0])!=0,'source compatibility failure at radial Hessian anisotropy')
# For q0=u1*u2, |Hess_S q0|<=2; |kappa|<=1/4 gives lower support curvature >=1/2.
eq(1-2*s.Rational(1,4),s.Rational(1,2),'admissible endpoint curvature lower bound')
y=s.symbols('y',real=True);a0=s.symbols('a0',positive=True);primitive=s.log((1+y)/(1-y))-2*y
expr=2*y*y/(1-y*y)
eq(s.diff(primitive,y),2*expr,'interval full symmetric energy derivative')
phi1=2*s.log(s.cosh(y/2))+s.log(4);eq(s.diff(phi1,y),s.tanh(y/2),'interval moment gradient')
eq(s.diff(phi1,y,2),(1-s.tanh(y/2)**2)/2,'interval moment Hessian')
# Exact symbolic exponent and determinant bookkeeping.
A,Bd,dim=s.symbols('a b n',positive=True);theta0=Bd/(8*(A+Bd+1));alpha=64*dim*(dim+2)*(A+Bd+1)/Bd
eq(theta0/(8*dim*(dim+2)),1/alpha,'final reciprocal exponent')
ck(s.simplify(s.Rational(1,2)-A/(8*(A+Bd+1))-s.Rational(3,8)))>0,'core exponent exceeds 3/8')
for nd in range(3,31):
 for aa in [s.Integer(1),s.Integer(10),s.Integer(1000)]:
  for bb in [s.Rational(1,100),s.Rational(1,2),s.Integer(1)]:
   th=bb/(8*(aa+bb+1));ck(2*th<=s.Rational(3,8),'spectral division power margin')
# m=-ellprime; determinant of Ksharp uses +t m and Lsharp uses -(1-t)m.
t,lk,ll,ld=s.symbols('t lk ll ld');m0=lk-ll;lc=(1-t)*lk+t*ll
for val,target in [(lc+t*m0,lk),(lc-(1-t)*m0,ll)]:eq(val,target,'endpoint log determinant sign')
print(json.dumps({'status':'PASS','exact_assertions':N,'gaussian':{k:str(v) for k,v in {'mean_score':m,'curvature_defect':D,'R_energy':renergy,'DP_energy':denergy,'T_energy':Tenergy}.items()},'cube_average_L2_squared':str(err),'radial_facet_J':str(jac),'scope':'Exact independent interface diagnostics; no numerical replacement for analytic compactness, BV or proof verdict'},indent=2,sort_keys=True))
