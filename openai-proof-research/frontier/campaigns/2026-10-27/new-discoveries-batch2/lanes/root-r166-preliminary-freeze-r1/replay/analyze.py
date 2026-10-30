from pathlib import Path
import json,mpmath as m
m.mp.dps=35
L=Path(__file__).resolve().parent
rows=[]
for a in [m.mpf(x) for x in ['.02','.1','.4','1','1.6','1.9','1.98']]:
 phi=m.acos(1-a)/2
 for z in [m.mpf(x) for x in ['.01','.05','.2','.5','1','1.5','1.8','1.95','1.99']]:
  b=m.acos(1-z)/2
  h=lambda x:z+a-1+m.cos(2*x)
  j=m.quad(lambda x:h(x)**m.mpf('-2.5'),[0,phi])+m.quad(lambda x:h(x)**m.mpf('-2.5'),[0,b])
  g=z*z-2*(1-a)*z-2*a
  curv=(3*j+g/(z*(2-z)*a)**m.mpf('1.5'))/4
  T=lambda zz:m.quad(lambda x:(zz+a-1+m.cos(2*x))**m.mpf('-.5'),[0,phi])+m.quad(lambda x:(zz+a-1+m.cos(2*x))**m.mpf('-.5'),[0,m.acos(1-zz)/2])
  direct=m.diff(T,z,2)
  rows.append(dict(a=str(a),z=str(z),curvature=str(curv),derivative_discrepancy=str(abs(curv-direct))))
(L/'curvature.json').write_text(json.dumps(rows,indent=2)+'\n')
print('curvature rows',len(rows),'min',min(float(r['curvature']) for r in rows),'max discrepancy',max(float(r['derivative_discrepancy']) for r in rows))
# M_n = sum of the two incomplete beta integrals, a=1, z=u^2.
# Exact recurrence M_n=(2n-1)s M_(n-1)/(2n) - sqrt(az)(a^(n-1)+z^(n-1))/n.
import sympy as S
u=S.symbols('u',positive=True);s=1+u*u;M=S.pi;out=[]
for n in range(1,13):
 M=S.expand(S.Rational(2*n-1,2*n)*s*M-u*(1+u**(2*n-2))/n)
 D=S.expand((u*S.diff(M,u,2)-S.diff(M,u))/(4*u**3))
 f=S.lambdify(u,D,'mpmath');samples=[(m.exp(m.mpf(k)/10),None) for k in range(-50,51)]
 vals=[f(x) for x,y in samples]
 out.append(dict(n=n,M=str(M),D=str(D),sample_min=str(min(vals)),sample_count=len(vals)))
(L/'moments.json').write_text(json.dumps(out,indent=2)+'\n')
print('moment rows',len(out),'sample minima',[(x['n'],x['sample_min']) for x in out])
