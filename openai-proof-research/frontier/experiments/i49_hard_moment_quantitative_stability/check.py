#!/usr/bin/env python3
"""Read-only exact diagnostics. Finite tests do not certify the analytic theorem."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,itertools
S=Path(__file__).resolve().parents[2]/'sources/i49_hard_moment_quantitative_stability'
for p in sorted((S/'vendor').glob('*.whl')):sys.path.insert(0,str(p))
import sympy as s
COUNT=0
def check(value,label):
 global COUNT
 assert bool(value),label
 COUNT+=1
def zero(value,label):check(s.cancel(s.expand(value))==0,label)
def mean(poly,x,widths):
 poly=s.Poly(s.cancel(s.expand(poly)),*x);out=0
 for exps,coeff in poly.terms():
  if any(k%2 for k in exps):continue
  out+=coeff*s.prod(a**k/s.Integer(k+1) for a,k in zip(widths,exps))
 return s.factor(out)
def monomials(x,degree):
 return [s.prod(xx**k for xx,k in zip(x,ks)) for ks in itertools.product(range(degree+1),repeat=len(x)) if sum(ks)<=degree]
hard=[]
for case in range(3):
 n=3;x=s.symbols('x0:3',real=True)
 widths=[s.Rational(1),s.Rational(3,2),s.Rational(5,4)]
 tau=[(a*a-xx*xx)/2 for a,xx in zip(widths,x)]
 T=s.diag(*tau)
 v=[x[0]*x[1]+x[2]**2,
    x[0]**2*x[1]**2/7+x[0]*x[2]**3/11+x[1]**2/3,
    (x[0]+2*x[1]-x[2])**4/23+x[0]*x[1]/5][case]
 h=s.hessian(v,x);P=T*h;B=P*T
 W=s.Matrix([-sum(s.diff(B[a,k],x[k]) for k in range(n)) for a in range(n)])
 Ws=P*s.Matrix(x)-s.Matrix([sum(tau[k]*s.diff(P[a,k],x[k]) for k in range(n)) for a in range(n)])
 for a in range(n):zero(W[a]-Ws[a],f'row adjunction {case} {a}')
 DzW=W.jacobian(x)*T;RR=DzW-B
 for a in range(n):
  for k in range(n):
   zero(DzW[a,k]-DzW[k,a],f'source gradient symmetry {case} {a} {k}')
   zero((P*T)[a,k]-(T*P.T)[a,k],f'P symmetry {case} {a} {k}')
  for sign in [-1,1]:zero(W[a].subs(x[a],sign*widths[a]),f'zero normal trace {case} {a} {sign}')
 u=-sum(s.diff(W[k],x[k]) for k in range(n))
 zero(mean(u,x,widths),f'hard centered score {case}')
 for k,g in enumerate(monomials(x,3)):
  ug=mean(u*g,x,widths)
  wg=mean(sum(W[i]*s.diff(g,x[i]) for i in range(n)),x,widths)
  bg=mean(sum(B[i,j]*s.diff(g,x[i],x[j]) for i in range(n) for j in range(n)),x,widths)
  zero(ug-wg,f'first adjunction {case} {k}')
  zero(ug-bg,f'second adjunction {case} {k}')
 # Invariant derivative norm in diagonal moment coordinates, integrated exactly.
 derivative=sum(tau[k]*tau[l]/tau[a]*s.diff(P[a,k],x[l])**2
                for a in range(n) for k in range(n) for l in range(n))
 derivative=s.cancel(derivative)
 rnorm=s.cancel(sum(RR[a,k]**2/(tau[a]*tau[k]) for a in range(n) for k in range(n)))
 # Normalized tensors use independent positive t symbols; only then substitute tau.
 tt=s.symbols('t0:3',positive=True)
 KK={}
 for a,k,l in itertools.product(range(n),repeat=3):
  KK[a,k,l]=s.sqrt(tt[a]*tt[k]*tt[l])*s.diff(v,x[a],x[k],x[l])
  if a==l:KK[a,k,l]-=x[a]*s.sqrt(tt[k])*h[a,k]
 knorm=s.expand(sum(q*q for q in KK.values()),force=True)
 symnorm=s.expand(sum((sum(KK[p] for p in itertools.permutations((a,k,l)))/6)**2
                      for a,k,l in itertools.product(range(n),repeat=3)),force=True)
 knorm=s.simplify(knorm).subs(dict(zip(tt,tau)))
 symnorm=s.simplify(symnorm).subs(dict(zip(tt,tau)))
 zero(knorm-derivative,f'invariant derivative normalization {case}')
 DW=W.jacobian(x);tensor=mean(s.trace(DW*DW),x,widths)
 rbudget=mean(rnorm,x,widths);dbudget=mean(derivative,x,widths);sbudget=mean(symnorm,x,widths)
 zero(tensor-rbudget-dbudget/2-3*sbudget/2,f'retained hard tensor identity {case}')
 zero(mean(u*u,x,widths)-tensor,f'hard vector Bochner {case}')
 check(dbudget>0 and rbudget>=0 and tensor>=dbudget/2,f'finite nonzero derivative budget {case}')
 hard.append({'case':case,'tensor':str(tensor),'R_square':str(rbudget),'derivative':str(dbudget)})
 # Matrix square is genuinely different from the Hilbert--Schmidt square.
 if case==2:
  check(mean(s.trace(DW*DW.T),x,widths)!=tensor,'matrix-square negative control')

# Constant box dilation fields, signed flux and nonzero score mean.
n=3;x=s.symbols('y0:3',real=True);widths=[s.Rational(1),s.Rational(2),s.Rational(3,2)]
b=[s.Rational(2,3),s.Rational(-3,5),s.Rational(4,7)]
W=s.Matrix([-b[i]*x[i] for i in range(n)]);m=-sum(b)
for k,g in enumerate(monomials(x,5)):
 lhs=mean(sum(W[i]*s.diff(g,x[i]) for i in range(n)),x,widths)
 boundary=0
 for i in range(n):
  xx=[x[j] for j in range(n) if j!=i];aa=[widths[j] for j in range(n) if j!=i]
  boundary+=b[i]*sum(mean(g.subs(x[i],sign*widths[i]),xx,aa) for sign in [-1,1])/2
 zero(lhs+boundary+m*mean(g,x,widths),f'nonzero-mean box boundary identity {k}')
check(m!=0,'mean score deliberately nonzero')
eps=s.symbols('epsilon',positive=True)
zero(-sum(s.diff(W[i],x[i]) for i in range(n))+eps*sum(x[i]*W[i] for i in range(n))
     -(sum(b)-eps*sum(b[i]*x[i]**2 for i in range(n))),'Gaussian bulk correction')

# Constant dual affine covariance on an oblique frame.
G=s.Matrix([[1,1,0],[0,1,1],[0,0,1]])
P=s.diag(-b[0],-b[1],-b[2]);tau=s.diag(s.Rational(2,5),s.Rational(3,7),s.Rational(4,9))
Pp=G.T*P*G.T.inv();tp=G.T*tau*G
check(Pp!=Pp.T,'oblique matrix need not be Euclidean symmetric')
check(Pp*tp==tp*Pp.T,'oblique Hessian symmetry')
zero(s.trace(Pp)-s.trace(P),'trace is invariant')
normal=s.Matrix([1,2,3]);position=s.Matrix([s.Rational(1,2),-1,2])
xp=G.T*position;up=G.inv()*normal
zero((Pp*xp).dot(up)-(P*position).dot(normal),'unnormalized flux covariance')
zero(xp.dot(up)-position.dot(normal),'support contact covariance')

# Product averaging on a cube is an actual integral, not a line restriction.
z=s.symbols('z0:3',real=True);eta=s.symbols('eta',positive=True)
phi=sum(q*q for q in z)/2+eta*(z[0]**2*z[1]**2+z[1]**2*z[2]**2)/16
grad=[s.diff(phi,q) for q in z];averages=[]
for i in range(3):
 other=[z[j] for j in range(3) if j!=i]
 fi=grad[i]
 for zz in other:fi=s.integrate(fi,(zz,-1,1))/2
 averages.append(s.factor(fi))
 zero(fi.subs(z[i],-z[i])+fi,f'odd averaged factor {i}')
err=mean(sum((grad[i]-averages[i])**2 for i in range(3)),z,[1,1,1])
mixed=mean(sum(s.diff(grad[i],z[j])**2 for i in range(3) for j in range(3) if i!=j),z,[1,1,1])
check(s.simplify(err/eta**2)>0,'nonzero averaging error')
check(s.simplify((4*mixed-err)/eta**2)>0,'transverse Poincare diagnostic')
for zz in itertools.product([-1,0,1],repeat=3):
 H=s.hessian(phi,z).subs(dict(zip(z,zz))).subs(eta,s.Rational(1,8))
 for k in [1,2,3]:check(H[:k,:k].det()>0,'convex core fixture')

# Product surface area transport and endpoint signs, with independent side lengths.
d=[s.Rational(1),s.Rational(3,2),s.Rational(5,4)]
scales=[s.Rational(2),s.Rational(3,2),s.Rational(4,3)]
vol=s.prod(2*dd for dd in d);det=s.prod(scales)
for i in range(3):
 area=s.prod(2*d[j] for j in range(3) if j!=i)
 newarea=s.prod(2*d[j]*scales[j] for j in range(3) if j!=i)
 zero(newarea-area*det/scales[i],f'block surface Jacobian {i}')
newvol=s.prod(2*d[i]*scales[i] for i in range(3))
zero(newvol-vol*det,'product volume determinant')
mixedself=sum(d[i]*scales[i]*2*s.prod(2*d[j]*scales[j] for j in range(3) if j!=i) for i in range(3))/3
zero(mixedself-newvol,'mixed volume normalization')

# A genuine nonsmooth three-dimensional cap family.
t=s.symbols('t',positive=True)
cutvol=8-t**3/3
axisarea=4-t**2/2;diagarea=s.sqrt(3)*t**2/2
divvol=(6*axisarea+2*diagarea*(3-t)/s.sqrt(3))/3
zero(divvol-cutvol,'cut cube cone-volume identity')
for a in [s.Rational(1,2),s.Rational(1,10),s.Rational(1,1000)]:
 check((8-cutvol).subs(t,a)==a**3/3,'three-dimensional exact removed cap volume')
 check(diagarea.subs(t,a)>0,'small active normal mass retained')

# A Euclidean Neumann solution need not be a moment-source gradient.
A=s.Matrix([[0,1,0],[1,0,0],[0,0,0]])/2
zz=s.Matrix([1,0,1]);radial_tau=s.eye(3)+zz*zz.T/7
check(A*radial_tau!=radial_tau*A,'ball Neumann moment-gradient negative control')
v=-z[0]*z[1]/2
zero(sum(s.diff(v,zz,2) for zz in z),'Neumann harmonic solution')
zero(sum(z[i]*s.diff(v,z[i]) for i in range(3))+z[0]*z[1],'Neumann sphere flux')

# The hard moment spectral load is outside the ordinary form dual.
y=s.symbols('y',real=True);a=s.symbols('a',positive=True)
f=s.log(1-y*y);tau=(1-y*y)/2
zero(tau*s.diff(f,y)+y,'interval hard flux')
primitive=s.log((1+a)/(1-a))-2*a
zero(s.diff(primitive,a)-2*a*a/(1-a*a),'truncated inverse energy derivative')
zero(primitive.subs(a,0),'truncated inverse energy constant')
check(s.limit(primitive,a,1,dir='-')==s.oo,'logarithmic inverse divergence')
q=s.symbols('q',positive=True)
phi=2*s.log(s.cosh(q/2))+s.log(4)
check(s.simplify(s.diff(phi,q,2)-(1-s.tanh(q/2)**2)/2)==0,'interval moment Hessian')

# Exact exponent inequalities: independent dimensional choices can be arbitrary here.
for n in range(3,13):
 for aa,bb in [(1,s.Rational(1)),(17,s.Rational(1,100)),(1000,s.Rational(1,1000000))]:
  theta=bb/(8*(aa+bb+1));core=s.Rational(1,2)-aa/(8*(aa+bb+1))
  check(theta>0 and theta<=s.Rational(1,8),'positive dimensional power')
  check(core>=s.Rational(3,8) and core>=2*theta,'soft-free hard core budget')
  normal=theta/(4*(n+2));endpoint=normal/(2*n)
  zero(endpoint-theta/(8*n*(n+2)),'final power balance')
  check(theta/4>=normal and theta/(2*(n+2))>=normal,'residual and volume subordinate')

print(json.dumps({'status':'PASS','exact_assertions':COUNT,
 'hard_field_cases':hard,'product_averaging_L2_squared':str(err),
 'scope':'Exact finite algebra, adjunction, geometry and rate diagnostics; not analytic proof or significance approval'},
 indent=2,sort_keys=True))
