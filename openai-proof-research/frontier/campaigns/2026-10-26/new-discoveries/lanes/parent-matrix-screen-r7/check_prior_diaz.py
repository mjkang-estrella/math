"""Check the closest published claimed counterexample at its actual bounds."""
import json
from pathlib import Path
import sympy as S

X=S.Matrix([[S.Rational(5,6),2],[2,5]])
Y=S.Matrix([[1,3],[3,10]])
d=S.sqrt(6); r=S.trace(X.inv()*Y)
assert d*d==Y.det()/X.det()
M=(X+Y)/2; K=S.Rational(303601,2200)
assert K==(11+S.Rational(1,50))**2/(4*11*S.Rational(1,50))
D=(K*(Y+d*X)**2/(r+2*d)-M*M).applyfunc(S.simplify)
p=S.simplify(D[0,0]);det=S.simplify(D.det())
assert p.is_positive and det.is_positive
for Z in [X,Y]:
    for H in [Z-S.eye(2)/50,11*S.eye(2)-Z]:
        assert H[0,0]>0 and H.det()>0
out={'source':'Hoa-Binh-Ho,2015 Remark1 p6; actual same matrices Eq4 p3',
 'm':'1/50','M':11,'K':str(K),'r':str(r),
 'positive_leading_minor':str(p),'positive_determinant':str(det),
 'verdict':'The printed claimed negative determinant -4.1122 is wrong at the stated bounds; this example does NOT refute the inequality.', 'credit':0}
Path('prior-diaz-correction.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
