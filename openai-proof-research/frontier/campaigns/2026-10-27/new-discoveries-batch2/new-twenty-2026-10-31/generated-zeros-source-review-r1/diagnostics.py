from pathlib import Path
import sympy as s,json,datetime,hashlib
p=Path(__file__).resolve().parent;z=s.symbols('z');c=[1,-1,0]; rows=[]
for k in range(15):
 n=3*k+2;P=sum(c[(n-j)%3]*z**j for j in range(n+1)); target=z*(z-1)*sum(z**(3*j) for j in range(k+1));assert s.expand(P-target)==0;assert s.degree(P,z)==n;rows.append({'k':k,'degree':n,'constant':0,'factor_identity':True})
A=z*(z-1)/(1-z**3)
assert s.cancel(A*(1-z**(3*(4+1)))-z*(z-1)*sum(z**(3*j) for j in range(5)))==0
(p/'diagnostics.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sympy':s.__version__,'finite_checks_only':rows,'symbolic_bridge':'P_(3k+2)=A(z)*1^k + (-A(z)*z^3)*(z^3)^k; A=z(z-1)/(1-z^3). Universal identity proved in REVIEW.md by coefficient grouping, not by finite tests.'},indent=2));print('15 exact polynomial identity/degree checks passed; finite diagnostics only')
