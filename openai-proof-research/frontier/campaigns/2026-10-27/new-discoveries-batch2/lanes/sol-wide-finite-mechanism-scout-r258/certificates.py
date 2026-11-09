from retrieve import *
import sympy as S
z=S.symbols('z');g=S.Poly(z**7+z**6-z**4-z**2-z-1,z,modulus=3)
r=S.Poly(z,z,modulus=3);rows=[]
for i in range(1,8):
 r=(r**3).rem(g);rows.append({'i':i,'remainder':str(r.as_expr())})
q,r1=S.div(S.Poly(z**11+z+1,z,modulus=3),g);assert r1.is_zero
r40=S.Poly(z**40,z,modulus=3).rem(g)
out={'g':str(g.as_expr()),'frobenius_remainders':rows,'g_values_F3':[int(g.eval(i))%3 for i in range(3)],'x11_x_1_quotient':str(q.as_expr()),'x40_remainder':str(r40.as_expr())}
(L/'polynomial-certificate.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
