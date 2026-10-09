"""Independent symbolic checks. No author modules are imported.
Run with Python 3; pinned pure-Python wheels are read directly without installation.
These exact identities are diagnostics, not a substitute for the universal proof.
"""
from pathlib import Path
import sys, json, hashlib
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
for wheel in sorted((HERE/'vendor').glob('*.whl')): sys.path.insert(0,str(wheel))
import sympy as s
x,y,z=s.symbols('x y z')
h=[s.Integer(1),(x+y)/2,x*y,x*y*(x+y)/2,x*x*y*y]
skew=[y-x,y*y-x*x,x*y*(y-x)]
J=(y-x)**2
mon=[x**i*y**j for i in range(3) for j in range(3)]
C=s.Matrix([[s.expand(f).coeff(x,i).coeff(y,j) for f in h+skew+[J]] for i in range(3) for j in range(3)])
assert C.det()!=0
assert [s.expand(f.subs(y,x)) for f in h]==[x**i for i in range(5)]
assert [s.diff(f,y).subs(y,x) for f in skew+[J]]==[1,2*x,x*x,0]
print('basis and transverse derivatives PASS',flush=True)
# Möbius graph restriction: nine exact polynomial identities and identity specialization.
a,b,c=s.symbols('a b c');phi=(a*z+b)/(c*z+1)
weighted=[s.cancel((c*z+1)**2*f.subs({x:z,y:phi})) for f in mon]
assert all(s.denom(w)==1 and s.degree(w,z)<=4 for w in weighted)
WH=s.Matrix([[s.expand(s.cancel((c*z+1)**2*f.subs({x:z,y:phi}))).coeff(z,i) for f in h] for i in range(5)])
assert WH.subs({a:1,b:0,c:0})==s.eye(5)
# Formal tail Jacobian determinant; the weights are deliberately arbitrary nonzero symbols.
t4,t5,t6,m4,m5,m6=s.symbols('t4 t5 t6 mu4 mu5 mu6')
AJ=s.Matrix([[m4,m5,m6],[2*m4*t4,2*m5*t5,2*m6*t6],[m4*t4*t4,m5*t5*t5,m6*t6*t6]])
assert s.expand(AJ.det()-2*m4*m5*m6*(t5-t4)*(t6-t4)*(t6-t5))==0
L=s.Matrix([[1,0,1],[1,0,-1],[0,2,0]]);S=s.diag(-1,1,1);J0=s.Matrix([[0,0,1],[0,-2,0],[1,0,0]])
assert L.T*S*L==-2*J0
assert -2*L.inv().T*J0*L.inv()==S
print('universal Möbius degree, Jacobian and congruence identities PASS',flush=True)
# Whole rational functions in THREE independent tail variables, not numerical jets.
T=list(map(s.Integer,[0,1,-1,2,-2,3]));u,v,w=s.symbols('u v w');U=T[:3]+[u,v,w]
H=s.Matrix([[f.subs({x:t,y:r}) for f in h] for t,r in zip(T,U)])
# Block solve avoids constructing any author formula implementation.
Hinv=H[:5,:].inv(); residual_row=s.Matrix([[*list(-H[5,:]*Hinv),1]])
R=[]
for f in skew+[J]:
 vals=s.Matrix([f.subs({x:t,y:r}) for t,r in zip(T,U)])
 R.append(s.factor(s.cancel((residual_row*vals)[0])))
print('three-variable residuals computed',flush=True)
subs0={u:T[3],v:T[4],w:T[5]}; columns=[]
for k,var in enumerate([u,v,w]):
 future=dict(zip([u,v,w][k+1:],T[4+k:]))
 previous=dict(zip([u,v,w][k:],T[3+k:]))
 columns.append([s.factor(s.cancel((f.subs(future)-f.subs(previous))/(var-T[3+k]))) for f in R])
A=s.Matrix(3,3,lambda i,j:columns[j][i]);br=s.Matrix([[col[3] for col in columns]])
assert all(s.cancel(R[i]-sum(A[i,j]*([u,v,w][j]-T[3+j]) for j in range(3)))==0 for i in range(3))
assert s.cancel(R[3]-(br*s.Matrix([u-T[3],v-T[4],w-T[5]]))[0])==0
assert all(s.denom(f).subs(subs0)!=0 for col in columns for f in col)
assert A.subs(subs0).det()!=0 and br.subs(subs0)==s.zeros(1,3)
print('removable quotient and exact ideal identities PASS',flush=True)
correction=(br*A.inv()).applyfunc(lambda f:s.factor(s.cancel(f)))
f=J-sum(correction[i]*skew[i] for i in range(3))
d=(Hinv*s.Matrix([f.subs({x:t,y:r}) for t,r in zip(T[:5],U[:5])])).applyfunc(lambda f:s.factor(s.cancel(f)))
q=s.Poly(s.expand(f-sum(d[i]*h[i] for i in range(5))),x,y)
coeff=[s.factor(s.cancel(q.coeff_monomial(term))) for term in mon]
assert all(s.denom(f).subs(subs0)!=0 for f in coeff)
assert s.expand(sum(f.subs(subs0)*term for f,term in zip(coeff,mon))-J)==0
Delta=s.lcm([s.denom(f) for f in coeff]); E=[s.cancel(Delta*f) for f in coeff]
assert Delta.subs(subs0)!=0 and all(s.denom(f)==1 for f in E)
for t,r in zip(T,U):
 assert s.expand(sum(f*t**i*r**j for f,(i,j) in zip(E,[(i,j) for i in range(3) for j in range(3)])))==0
print('three-variable cleared polynomial certificate: all six identities PASS',flush=True)
# F=Q(sqrt(2)) tensor F: present it as F[r]/(r^2-2).
# This is an adversarial descent test in a genuinely non-domain tensor ring.
# Local certificate for t_i=i*sqrt(2) on the dependent family U_i=i*r:
# q_loc=(y-(r/sqrt(2))*x)^2 has diagonal J and vanishes identically.
# Deliberately choose Delta=r+sqrt(2), a local unit whose tensor image is a zero divisor.
r=s.symbols('r');root=s.sqrt(2)
qdep=(y-r*x/root)**2;delta=r+root
edep=s.Poly(s.expand(delta*qdep),x,y)
kn=[s.rem(s.expand(edep.coeff_monomial(term)/(2*root)),r*r-2,r,extension=root) for term in mon]
assert s.rem((r+root)*(r-root),r*r-2,r,extension=root)==0
assert s.rem(r+root,r*r-2,r,extension=root)!=0 and s.rem(r-root,r*r-2,r,extension=root)!=0
for i in range(6):
 assert s.rem(s.expand(sum(k*(i*root)**a*(i*r)**b for k,(a,b) in zip(kn,[(a,b) for a in range(3) for b in range(3)]))),r*r-2,r,extension=root)==0
assert s.expand(sum(k.subs(r,root)*term for k,term in zip(kn,mon))-J)==0
print('algebraic dependency / zero-divisor descent stress test PASS',flush=True)
# Seven-point second-order obstruction with seven rational nodes is only a polynomial identity test;
# the proof uses algebraically independent nodes for the right-factor ring homomorphism.
T7=list(map(s.Rational,[-4,-2,0,1,3,5,8]));weights=[1/s.prod(t-u for u in T7 if t!=u) for t in T7]
moments=[sum(l*t**j for l,t in zip(weights,T7)) for j in range(7)]
assert moments==[0]*6+[1]
zeta=s.symbols('zeta');q0,q1,q2,q3=s.symbols('q0 q1 q2 q3');Q1=q0*J+sum(k*f for k,f in zip([q1,q2,q3],skew));der=s.expand(s.diff(Q1,y).subs({x:zeta,y:zeta}))
assert s.degree(der,zeta)<=2
assert s.expand(sum(l*(t**6+t**3*der.subs(zeta,t)) for l,t in zip(weights,T7)))==1
# Geometric boundary checks: rank 5 for six circle nodes; rank 6 for octahedron.
cp=[[(1-t*t)/(1+t*t),2*t/(1+t*t)] for t in T]
def rows(points):
 return s.Matrix([[a*b for a in [1]+p for b in [1]+p] for p in points])
assert rows(cp).rank()==5
sphere3=[[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]]
assert rows(sphere3).rank()==6
result={'status':'PASS','sympy_version':s.__version__,'basis_determinant':str(C.det()),'mobius_monomials':9,'tail_variables':['u','v','w'],'nodes':list(map(str,T)),'residuals':list(map(str,R)),'A':[[str(A[i,j]) for j in range(3)] for i in range(3)],'b':list(map(str,br)),'correction':list(map(str,correction)),'coefficient_order':[[i,j] for i in range(3) for j in range(3)],'certificate_coefficients':list(map(str,coeff)),'cleared_coefficients':list(map(str,E)),'Delta':str(s.factor(Delta)),'Delta_at_diagonal':str(Delta.subs(subs0)),'exact_polynomial_evaluation_identities':6,'removable_quotients':12,'zero_divisor_descent':{'field':'Q(sqrt(2))','tensor_presentation':'F[r]/(r^2-2)','Delta':'r+sqrt(2)','normalizer':'1/(2sqrt(2)) in LEFT field','certificate_coefficients':list(map(str,kn)),'evaluation_identities':6},'seven_moments':list(map(str,moments)),'geometric_ranks':{'six_circle_points':5,'octahedron':6},'scope':'Exact symbolic diagnostics; not a replacement for the universal local-ring proof.'}
(HERE/'independent-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print('ALL INDEPENDENT CHECKS PASS',flush=True)
