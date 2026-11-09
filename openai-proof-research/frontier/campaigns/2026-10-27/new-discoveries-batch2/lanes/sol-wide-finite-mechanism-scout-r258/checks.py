from retrieve import *
import sympy as S
a,z=S.symbols('a z');f=a**7+a**6+a**5-a**4+a**3-a**2-1;T=1+a+a*a+a**3
rem=lambda v:S.Poly(v,a,modulus=3).rem(S.Poly(f,a,modulus=3)).as_expr()
P=lambda v:S.Poly(v,a,modulus=3)
assert S.div(P(T**4-a),P(f))[1].is_zero
assert S.gcd(P(f),P(a**5-1)).degree()==0
assert S.gcd(P(f),P(a**4-1)).degree()==0
assert S.gcd(P(f),P(a-1)).degree()==0
r=P(a)
for i in range(7):r=(r**3).rem(P(f))
assert (r-P(a)).is_zero
assert S.gcd(P(f),P(a**3-a)).degree()==0
# Rabin criterion: degree 7 prime; these checks prove irreducibility.
normtest=rem(T**1)
def pw(v,e):
 r=1
 while e:
  if e&1:r=rem(r*v)
  v=rem(v*v);e//=2
 return r
leg=pw(T,(3**7-1)//2)
res=S.Poly(S.resultant(f,z*z-T,a),z,modulus=3).monic()
print('f',f,'T_character',leg,'resultant',res.as_expr())
# Use square root in F_(3^14), whether or not it already belongs to F_(3^7).
checks={'f_irreducible_Rabin':True,'T4_minus_a_remainder':str(rem(T**4-a)),'a5_minus1_coprime':True,'denominators_nonzero':True,'T_quadratic_character':str(leg),'x_polynomial':str(res.as_expr()),'source_q':3,'source_n':14,'source_d':2}
assert leg in [1,-1]
# Direct x-polynomial route; x^8=a, so test the literal trace R=x+x^11.
Q=res
def zp(v,e):
 r=S.Poly(1,z,modulus=3);v=S.Poly(v,z,modulus=3)
 while e:
  if e&1:r=(r*v).rem(Q)
  v=(v*v).rem(Q);e//=2
 return r
R=S.Poly(z+z**11,z,modulus=3)
assert (zp(R.as_expr(),3)-R).rem(Q).is_zero
assert S.gcd(Q,S.Poly(z**40-1,z,modulus=3)).degree()==0
assert S.gcd(Q,S.Poly(z**8-1,z,modulus=3)).degree()==0
assert (zp(z,3**14)-S.Poly(z,z,modulus=3)).rem(Q).is_zero
checks.update(direct_R3_minus_R_zero=True,direct_x40_minus1_coprime=True,direct_field_embedding=True)
(L/'checks.json').write_text(json.dumps(checks,indent=2));print(json.dumps(checks,indent=2))
