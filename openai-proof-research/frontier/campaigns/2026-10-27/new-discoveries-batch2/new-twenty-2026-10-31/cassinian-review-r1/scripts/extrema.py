import sympy as S
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];t=S.symbols('t',real=True)
rows=[]
for a,b in [(S.Integer(4),S.Integer(1)),(S.Integer(2),S.Rational(1,2))]:
 P=t*t*((t-a)**2+b*b); roots=S.solve(S.diff(P,t),t); eligible=[x for x in roots if x>=1]; candidates=[S.Integer(1),*eligible]
 vals=[S.simplify(P.subs(t,x)) for x in candidates];m=min(vals); c=S.sqrt((a*a+b*b)/m)
 rows.append(dict(a=str(a),b=str(b),polynomial=str(S.expand(P)),derivative=str(S.factor(S.diff(P,t))),critical=[str(x) for x in roots],candidates=[str(x) for x in candidates],values=[str(x) for x in vals],minimum=str(m),cassinian=str(S.simplify(c)),decimal=str(S.N(c,25)),P_at_infinity=str(S.limit(P,t,S.oo)),ratio_at_infinity='0'))
assert S.sqrt(S.Rational(17,10)) < S.Rational(7,4)
assert S.sqrt(17)/2 > S.Rational(7,4)
(D/'logs/extrema.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
