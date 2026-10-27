"""Reproduce the public registry's rational witness; no novelty credit."""
import json
from pathlib import Path
import sympy as S

A=S.Matrix([[9,0,2,0],[0,2,1,0],[2,1,1,0],[0,0,0,1]])
X=S.diag(1,1,0,0);Y=S.zeros(4);Y[2,0]=1;Y[3,1]=1
I=S.eye(4);m=S.Rational(1,25);M=S.Integer(13)
L=I.copy();L[2,0]=S.Rational(25,112);L[2,1]=S.Rational(25,49)
U=I.copy();U[2,0]=-S.Rational(1,2);U[2,1]=-S.Rational(1,11)
lo=[S.Rational(224,25),S.Rational(49,25),S.Rational(33,9800),S.Rational(24,25)]
hi=[S.Integer(4),S.Integer(11),S.Rational(120,11),S.Integer(12)]
assert all(x>0 for x in lo+hi)
assert A-m*I==L*S.diag(*lo)*L.T
assert M*I-A==U*S.diag(*hi)*U.T
assert X*X.T*X==X and Y*Y.T*Y==Y and X.T*Y==S.zeros(4)
assert X*X.T+Y*Y.T==I
def phi(z):return X*z*X.T+Y*z*Y.T
T=phi(X.T*A*Y)*phi(Y.T*A*Y).inv()*phi(Y.T*A*X)*phi(X.T*A*X).inv()
e=S.eye(4)[:,1];value=(e.T*T.T*T*e)[0];c=((M-m)/(M+m))**2
assert value==S.Rational(5,4) and value>c*c
out={'mathdb':324727,'verdict':'EXCLUDED: public prior refutation',
 'registry_commit':'f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada',
 'path':'D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.lean',
 'sha256':'2ac3abab071b99c38dc92966a7967b89315041a46e8817c042b8a122e1ecbb44',
 'independent_exact_check':{'LDL_bounds':True,'partial_isometries':True,'unital_CP_map':True,
   'tested_norm_square':str(value),'conjectured_bound':str(c)},'credit':0}
Path('prior-wielandt-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
