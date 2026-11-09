"""Independent exact rational matrix check of saved polynomial quotient claims."""
import json,signal
from pathlib import Path
import sympy as s
signal.alarm(50)
p=Path(__file__).parent;d=json.loads((p/'trace-exact-polynomials.json').read_text())
def read(xs):return {tuple(x['traces']):s.Rational(x['coefficient']) for x in xs}
low=list(map(read,d['lower_identity_products']));q=read(d['q']);delta=read(d['delta'])
rows=sorted(set().union(*[set(x) for x in low+[q,delta]]))
def v(x):return s.Matrix([x.get(k,0) for k in rows])
M=s.Matrix.hstack(*map(v,low));Mq=M.row_join(v(q));test=v(delta)+72*v(q)
# Exact DomainMatrix ranks use QQ; no floating point rank thresholds.
from sympy.polys.matrices import DomainMatrix
rank=lambda A:DomainMatrix.from_Matrix(A).convert_to(s.QQ).rank()
r={'rows':len(rows),'columns':len(low),'rank_lower':rank(M),'rank_with_q':rank(Mq),'rank_with_delta_plus_72q':rank(M.row_join(test)),'arithmetic':'SymPy QQ DomainMatrix'}
assert r['rank_lower']==104 and r['rank_with_q']==105 and r['rank_with_delta_plus_72q']==104
(p/'exact-verification.json').write_text(json.dumps(r,indent=2));print(r)
