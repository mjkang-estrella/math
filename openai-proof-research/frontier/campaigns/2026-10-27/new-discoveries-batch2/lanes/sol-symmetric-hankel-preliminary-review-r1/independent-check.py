import resource, signal, json
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912))
resource.setrlimit(resource.RLIMIT_CPU,(20,20)); signal.alarm(25)
import sympy as s
z=s.Symbol('z'); u=s.Symbol('u',real=True)
def jet(x,n=5): return s.series(x,z,0,n).removeO().expand()
w=z*z*(u+z)/(1+u*z)
p=jet(1+w+w*w/3-w*w*w/9)
E=(p+p.subs(z,-z))/2
G=s.integrate(s.cancel((E-1)/z),z)
q=jet(s.exp(G)); fp=jet(p*q); f=s.integrate(fp,z)
a=[s.expand(f).coeff(z,k) for k in range(1,6)]
M=s.Matrix([[a[0],a[1],a[2]],[a[1],a[2],a[3]],[a[2],a[3],a[4]]]); H=s.factor(M.det())
assert s.simplify(H-(u**4-u**3/3-1)/16)==0
assert [x.subs(u,s.Rational(1,4)) for x in a]==[1,0,s.Rational(1,8),s.Rational(15,64),-s.Rational(35,768)]
assert H.subs(u,s.Rational(1,4))==-s.Rational(769,12288)
# Independent ODE recurrence, no exponential formula.
b={1:s.Integer(1)}
for n in range(2,6):
 rhs=sum(p.coeff(z,k)*b.get(n-k,0) for k in range(1,n))
 b[n]=s.expand(rhs/(n-(n%2)))
assert all(s.simplify(b[n]-a[n-1])==0 for n in range(1,6))
# Schur inversion at first parameter zero; |A|=u, |B|=v.
A,Ac,B,rho,v=s.symbols('A Ac B rho v'); C=-(1-u*u)*Ac*B**2+(1-u*u)*(1-v*v)*rho
ws=A*z*z+(1-u*u)*B*z**3+C*z**4
ps=jet(1+ws+ws**2/3-ws**3/9)
bs={1:s.Integer(1)}
for n in range(2,6):bs[n]=s.expand(sum(ps.coeff(z,k)*bs.get(n-k,0) for k in range(1,n))/(n-n%2))
hs=s.expand(s.Matrix([[1,bs[2],bs[3]],[bs[2],bs[3],bs[4]],[bs[3],bs[4],bs[5]]]).det()).subs(Ac*A,u*u).expand()
expected=-A**3/48-(1-u**4)*B**2/16+A*(1-u*u)*(1-v*v)*rho/8
assert s.simplify(hs-expected)==0
# At A=u>0,B=1 all surviving phase-group terms are negative.
phase_terms=[-u**3/48,-(1-u**4)/16]
assert s.simplify(sum(phase_terms)-H)==0
published_edge=-20736*u**4+6912*u**3+20736
assert s.simplify(published_edge+331776*H)==0
assert published_edge.subs(u,s.Rational(1,4))==20763
# Actual published determinant polynomial at l1=0, independently transcribed
# from indexed primary Section 2 (search5.json).
l2,l3,l4=s.symbols('l2 l3 l4')
pub=(-6048*l2**3+10368*l2*l4-5184*l3**2)/331776
pubslice=pub.subs({l2:2*A,l3:2*(1-u*u)*B,l4:2*A**2+2*C}).expand().subs(Ac*A,u*u).expand()
assert s.simplify(pubslice-expected)==0
# Caratheodory lemma l1=0 alpha=u beta=1 yields l2,l3,l4.
car=jet((1+w)/(1-w));carcoeff=[s.factor(car.coeff(z,k)) for k in range(1,5)]
assert all(s.simplify(a-b)==0 for a,b in zip(carcoeff,[0,2*u,2-2*u*u,2*u*(u*u+u-1)]))
x,y=s.symbols('x y',real=True); zz=x+s.I*y
assert s.expand((1+u*zz)*(1+u*s.conjugate(zz))-(u+zz)*(u+s.conjugate(zz))-(1-u*u)*(1-x*x-y*y))==0
out={'pass':True,'method':'independent symbolic Taylor integration plus ODE recurrence; Schur inversion and phase alignment','coefficients':[str(t.subs(u,s.Rational(1,4))) for t in a],'H':str(H.subs(u,s.Rational(1,4))),'gap':str(-H.subs(u,s.Rational(1,4))-s.Rational(1,16)),'Schur_H':str(expected),'Caratheodory_coefficients':list(map(str,carcoeff)),'phase_terms_at_quarter':[str(t.subs(u,s.Rational(1,4))) for t in phase_terms],'published_edge_value':20763,'limits':{'AS':536870912,'CPU':20,'alarm_wall':25,'outer_wall':30,'BLAS':1}}
print(json.dumps(out,indent=2))
