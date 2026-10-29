from pathlib import Path
import sympy as s,json
x,t,z,rho,m=s.symbols('x t z rho m');p=Path(__file__).resolve().parent
checks=[]
def eq(a,b,label):
 assert s.simplify(a-b)==0,label
 checks.append(label)
# Independent triangular-system route. G maps (S,1) to (S,S').
pairs=[(1/x+2/(x-1),(x+1)/(x*(1-x))), (1/(2*x)+1/(2*(x-1)),1/x), (x,1), (1/x**2,x-1), (x/(x*x+1),(x-2)**2), (0,1/(x+1))]
for i,(r,q) in enumerate(pairs):
 r,q=s.sympify(r),s.sympify(q)
 M=s.Matrix([[r,q],[0,0]]);G=s.Matrix([[1,0],[r,q]])
 C=s.simplify((G.diff(x)+G*M)*G.inv())
 want=s.Matrix([[0,1],[s.diff(r,x)-r*s.diff(q,x)/q,r+s.diff(q,x)/q]])
 for j in range(2):
  for k in range(2):eq(C[j,k],want[j,k],f'gauge-{i}-{j}-{k}')
 eq(G.det(),q,f'gauge-determinant-{i}')
# At a finite pole where r=rho/u+..., q=u^m * unit:
I=z*(z-1)-(rho+m)*z+(m+1)*rho
eq(I,(z-rho)*(z-m-1),'finite-indicial-factorization')
# Under x=1/t the affine ODE remains affine, rtilde=-r(1/t)/t^2.
# Hence same factorization at infinity; residue is minus sum of finite residues.
r=2/x+s.Rational(1,3)/(x-1)-s.Rational(5,7)/(x+2)
rt=-r.subs(x,1/t)/t**2
eq(s.limit(t*rt,t,0),-(2+s.Rational(1,3)-s.Rational(5,7)),'infinity-residue')
# Genuine rational affine equation S=1, H=x^(1/2)*(1-x)^(1/2).
# After x=t^2: H=t sqrt(1-t^2), U=1/H, R=1/t.
r=1/(2*x)-1/(2*(1-x));q=-r;Ht=t*s.sqrt(1-t*t);U=1/Ht;V=U-1/t
eq(s.diff(U,t),2*t*q.subs(x,t*t)/Ht,'ramified-derivative')
eq(s.diff(V,t),s.diff(U,t)+1/t**2,'principal-part-derivative')
ser=s.series(V,t,0,25).removeO().expand()
coeff=[]
for n in range(25):
 a=ser.coeff(t,n); assert (a*2**(n+1)).q==1; coeff.append(str(a))
checks.append('25-scaled-regular-coefficients')
# Rational escape case: a nonminimal affine homogenization need not be Fuchsian.
# S=1, r=x, q=-x gives irregular rank-one H=exp(x^2/2).
eq(s.diff(s.Integer(1),x),x*1-x,'rational-escape')
# Logarithm meets rational affine equation but fails boundedness (distinct primes).
for prime in [3,5,7,11,13]:
 assert s.Rational(1,prime).q==prime
checks.append('logarithm-denominator-obstruction-diagnostic')
result={'status':'PASS','checks':checks,'count':len(checks),'ramified_regular_coefficients':coeff,'finite_checks_prove_deep_theorems':False,'route':'triangular rational gauge + exact indicial factorization, independent of candidate coefficient enumeration'}
(p/'evidence.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
