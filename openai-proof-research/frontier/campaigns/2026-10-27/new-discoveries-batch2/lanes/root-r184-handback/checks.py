"""Exact symbolic route diagnostics; no finite-node validation or universal claim."""
import json
from pathlib import Path
import sympy as S
L=Path(__file__).resolve().parent
x,k=S.symbols('x k',real=True); p=S.Function('p')(x);s=S.sqrt(1-x*x)
D=lambda f:-s*S.diff(f,x)
u=S.sqrt(s)*p;A=k*k+1/(4*s*s)
res=S.simplify((D(D(u))+A*u)/S.sqrt(s)-((1-x*x)*S.diff(p,x,2)-2*x*S.diff(p,x)+(k*k-S.Rational(1,4))*p))
assert res==0
U,V,a,b=S.symbols('U V a b',real=True)
flow=lambda f:S.diff(f,U)*V-S.diff(f,V)*a*U+S.diff(f,a)*b
assert S.expand(flow(V*V+a*U*U)-b*U*U)==0
assert S.simplify(flow(U*U+V*V/a)+b*V*V/(a*a))==0
# Squared upper-envelope comparison with dimensionless center c=73/72,
# k=3, sin(theta)^2=1/4: a method countermodel, not Legendre data.
c=S.Rational(73,72); raw=c*(9+1)/(9+S.Rational(1,4)); target_squared=S.Rational(9,8)
assert raw==S.Rational(365,333)
assert raw*raw>target_squared
out=dict(legendre_liouville_residual=str(res),sonin_energy_identity=True,sonin_envelope_identity=True,
 raw_normalized_envelope=str(raw),required_squared_envelope=str(target_squared),
 envelope_squared_excess=str(raw*raw-target_squared),
 interpretation='Exact method obstruction only. c is hypothetical; not an actual Legendre center or source refutation. No finite-node tests performed.')
text=json.dumps(out,indent=2)+'\n'
(L/'checks.json').write_text(text)
print(text,end='')
