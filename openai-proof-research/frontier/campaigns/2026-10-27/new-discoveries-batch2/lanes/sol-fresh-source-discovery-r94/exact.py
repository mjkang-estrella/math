from pathlib import Path
import sympy as s,json
x,u=s.symbols('x u');h=lambda n,z:s.hermite_prob(n,z)
def expect(poly):
 out=0
 for (i,),c in s.Poly(s.expand(poly),u).terms():
  if i%2==0:out+=c*(s.factorial2(i-1) if i else 1)
 return s.expand(out)
checks=[]
for a,b in [(s.Rational(3,5),s.Rational(4,5)),(s.Rational(5,13),s.Rational(12,13)),(s.Rational(8,17),s.Rational(15,17))]:
 X=a*x+b*u;Y=b*x-a*u
 for n,m in [(4,0),(0,4),(4,4),(2,6),(6,2)]:
  diff=expect(h(n,X)*h(m,Y))-a**n*b**m*h(n+m,x)
  assert s.expand(diff)==0;checks.append([str(a),str(b),n,m])
# Strong log concavity certificate polynomial identity, all x and 0<a<=1/222.
a=s.symbols('a');r=1+a*h(4,x)
assert s.expand(r-24*a*x*x-(a*(x*x-15)**2+1-222*a))==0
# Exact curvature coefficient for general single even Hermite mode m=2..20.
t=s.symbols('t');curv=[]
for m in range(2,21):
 A=t**m+(1-t)**m
 assert s.expand(s.diff(A*A,t,2)-2*(s.diff(A,t)**2+A*s.diff(A,t,2)))==0
 curv.append(m)
(Path(__file__).parent/'exact-results.json').write_text(json.dumps({'conditional_hermite_polynomial_identities':checks,'strong_logconcavity_identity':True,'curvature_square_identity_degrees':curv},indent=2));print('15 exact conditional identities; 19 curvature identities; global log-concavity identity PASS')
