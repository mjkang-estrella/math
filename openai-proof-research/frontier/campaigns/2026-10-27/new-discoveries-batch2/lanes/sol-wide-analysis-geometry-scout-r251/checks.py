from fractions import Fraction as F
import json
import sympy as S
z,a,b=S.symbols("z a b",real=True)
f=z*z-2*a*z+a*a+b*b
g=z**3/6
L=((3*a*a-b*b)*z-2*a*(a*a+b*b))/6
assert S.expand(g-L-f*(z+2*a)/6)==0
assert S.simplify(S.diff(g-L,z).subs(z,1)-(3-3*a*a+b*b)/6)==0
assert S.expand((3-3*a*a+b*b)/6-(1-a)-(b*b-3*(1-a)**2)/6)==0
# Independent recurrence for slope of interpolation of powers at a +/- ib:
# U_m=(w**m-conj(w)**m)/(w-conj(w)); U0=0,U1=1.
U=[S.Integer(0),S.Integer(1)]
for m in range(2,9):U.append(S.expand(2*a*U[-1]-(a*a+b*b)*U[-2]))
assert S.expand(U[3]-(3*a*a-b*b))==0
assert S.expand(U[4]-(4*a**3-4*a*b*b))==0
w=a+S.I*b
for m in range(1,9):assert S.expand((w**m-S.conjugate(w)**m)-2*S.I*b*U[m])==0
out=[]
for aa,bb,x in [(F(3,4),F(1,2),F(1)),(F(1,100),F(1,2),F(0))]:
 assert aa>0 and bb>0 and aa*aa+bb*bb<1
 slope=(3*aa*aa-bb*bb)/6
 error=abs(x*x/2-slope);baseline=abs(x-aa)
 assert error>baseline
 out.append(dict(a=str(aa),b=str(bb),x=str(x),norm_squared=str(aa*aa+bb*bb),error=str(error),baseline=str(baseline),gap=str(error-baseline)))
# Exact Q(i) interpolation checks at each of the two rational grids.
for aa,bb in [(S.Rational(3,4),S.Rational(1,2)),(S.Rational(1,100),S.Rational(1,2))]:
 for node in [aa+S.I*bb,aa-S.I*bb]:assert S.expand((g-L).subs({z:node,a:aa,b:bb}))==0
print(json.dumps({"status":"PASS","cases":out,"symbolic_identity":True,"independent_power_recurrence_degrees":[1,8]},indent=2))
