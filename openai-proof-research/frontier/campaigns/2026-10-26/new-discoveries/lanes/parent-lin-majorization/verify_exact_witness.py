#!/usr/bin/env python3
from pathlib import Path
import json, hashlib
import sympy as s
p=Path(__file__).resolve().parent
j=json.loads((p/'lin-rational-svd.json').read_text())
A,B,Q=[s.Matrix(j[k]) for k in ['A','B','Q']];D=s.diag(*map(s.Rational,j['D']))
assert A==A.T and B==B.T and Q.T*Q==s.eye(3) and Q*Q.T==s.eye(3)
assert A*B==Q*D and B*A==D*Q.T
assert (A*B).T*(A*B)==D**2
assert (B*A).T*(B*A)==(Q*D*Q.T)**2
L=A**2+Q*D**3*Q.T;R=A**2+D**3;tau=s.Rational(197,500)
assert L==s.Matrix(j['L']) and R==s.Matrix(j['R']) and s.trace(L)==s.trace(R)
v=s.Matrix([s.Rational(-19,100),-1,s.Rational(37,50)])
q=(v.T*(R-tau*s.eye(3))*v)[0]
assert q==s.Rational(-137006877457,21744240000000) and q<0
out={'status':'PASS: exact rational identities and positivity certificates; source spectral deduction in PROOF.md','credit':0,'trace':str(s.trace(L)),'R_shift_quadratic':str(q),'LDL':{}}
for name,M in [('A',A),('Bblock',B[:2,:2]),('Lshift',L-tau*s.eye(3))]:
 T,E=M.LDLdecomposition();assert T*E*T.T==M and T.det()==1 and all(E[i,i]>0 for i in range(M.rows))
 out['LDL'][name]={'lower':[[str(x)for x in T.row(i)]for i in range(T.rows)],'pivots':[str(E[i,i])for i in range(E.rows)],'leading_minors':[str(M[:i,:i].det())for i in range(1,M.rows+1)]}
assert B[:,2]==s.zeros(3,1) and B[2,:]==s.zeros(1,3)
(p/'exact-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
