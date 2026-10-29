import sympy as s,json,math
from pathlib import Path
P=Path(__file__).resolve().parent
t=s.sqrt(2)/2
B=s.Matrix([[t,t],[t,s.Rational(3,2)-t]])
M=s.zeros(4);M[:2,2:]=B;M[2:,:2]=B
assert M==M.T and all(M[i,i]==0 for i in range(4))
assert s.simplify(B.det()-(3*t/2-1))==0
assert s.simplify(B.trace())==s.Rational(3,2)
# t>2/3 since 1/2>4/9, so det>0 and B is positive definite.
assert s.Rational(1,2)>s.Rational(4,9)
# c=3/2-t lies between t and 1: t<3/4 and t>1/2.
assert s.Rational(1,2)<s.Rational(9,16) and s.Rational(1,2)>s.Rational(1,4)
I=s.eye(2);Q=I.row_join(I).col_join(I.row_join(-I))
assert Q*M*Q==s.diag(2*B,-2*B)
# Q/sqrt(2) orthogonal; energy(M)=2 trace(B)=3.
assert Q.T*Q==2*s.eye(4)
assert 2*B.trace()==3
# degree consistency fails: support is K2,2, so every literal weight must be t.
assert s.simplify(M[1,3]-t)!=0
x=s.symbols('x'); families=0
for p in range(1,21):
 for q in range(1,21):
  C=s.Matrix([[0,p],[q,0]])
  assert C.charpoly(x).as_expr()==x*x-p*q
  z=p*q*(p*p+q*q)
  assert math.isqrt(z)**2!=z
  families+=1
# A rational substitute positive definite B also defeats eigenvalue-by-eigenvalue reasoning.
R=s.Matrix([[2,1],[1,3]])
assert R.charpoly(x).as_expr()==x*x-5*x+5 and R.det()>0 and R.trace()==5
out={'status':'PASS','complete_bipartite_parameter_checks':families,'generic_source_range_matrix_energy':3,'rational_matrix_energy':10,'limits':'finite diagnostics, not a universal source proof'}
(P/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
