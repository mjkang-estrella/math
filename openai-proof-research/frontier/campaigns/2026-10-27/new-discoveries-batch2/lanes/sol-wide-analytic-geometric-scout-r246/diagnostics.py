import sympy as S, json, pathlib
L=pathlib.Path(__file__).resolve().parent
x,y,z,w,X,Y,Z=S.symbols('x y z w X Y Z',nonnegative=True)
s=x+y+z+w
Q=x*(x+y)*(x+y+z)
P=S.expand(Q+x*y*(1-x-y-z))
assert S.expand(P-(x*x*(x+y+z)+x*y))==0
u=[x,x*x+y,x**3+2*x*y+z]
cert=[x*(1-y-x*(x+y+z)), x*x*(1-x-y-z)+y*(1-x), x*y*(1-x)+z*(1-x*x)]
assert all(S.expand(a-P-b)==0 for a,b in zip(u,cert))
# Homogenize P at total barycentric degree three.
Ph=x*x*(x+y+z)+x*y*s
uh=[x*s*s,x*x*s+y*s*s,x**3+2*x*y*s+z*s*s]
out={'P':str(P),'gap_certificates':[str(v) for v in cert], 'bernstein':[]}
for a in uh:
 poly=S.Poly(S.expand(a-Ph),x,y,z,w)
 assert all(c>=0 for c in poly.coeffs())
 out['bernstein'].append(str(poly.as_expr()))
hat=S.expand(P.subs({x:X,y:Y-X,z:Z-Y},simultaneous=True))
assert S.expand(hat-(X*Y+X*X*(Z-1)))==0
assert S.Poly(hat.subs({Y:1,Z:1}),X).total_degree()<=1
assert S.Poly(hat.subs(Z,1),X,Y).total_degree()<=2
assert S.Poly(hat,X,Y,Z).total_degree()<=3
out['hat']=str(hat)
out['witness']={'Q':str(Q.subs({x:S.Rational(1,4),y:S.Rational(1,4),z:S.Rational(1,4)})), 'P':str(P.subs({x:S.Rational(1,4),y:S.Rational(1,4),z:S.Rational(1,4)}))}
n=0
for a in range(21):
 for b in range(21-a):
  for c in range(21-a-b):
   vals={x:S.Rational(a,20),y:S.Rational(b,20),z:S.Rational(c,20)}
   assert P.subs(vals)>=Q.subs(vals)
   assert all((v-P).subs(vals)>=0 for v in u)
   n+=1
out['exact_simplex_grid_points']=n
(L/'diagnostics.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
