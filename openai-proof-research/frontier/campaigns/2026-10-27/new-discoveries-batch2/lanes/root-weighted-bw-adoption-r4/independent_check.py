from pathlib import Path
import json
import sympy as s

def sq(M):return sum(x*x for x in M)
E=lambda n,i,j:s.eye(n)[:,i]*s.eye(n)[j,:]
I=s.eye(2);Y=E(2,0,1);T=I*Y-Y*I
example_n2=dict(T_sq=int(sq(T)),claimed_rhs=2*int(sq(I)*sq(Y)))
W=s.diag(2,1);X=E(2,0,1);Y=E(2,1,0);T=X*W*Y-Y*W*X
D=5*(sq(X)*sq(Y)-sum(X[i,j]*Y[i,j] for i in range(2) for j in range(2))**2)-sq(T)
example_sos=dict(actual_defect=int(D),claimed_sos=4)
checks=[]
for w in [[2,1],[9,4,1],[9,4,2,1]]:
 n=len(w);units=[E(n,i,j) for i in range(n) for j in range(n)]
 cols=[]
 for a in range(n*n):
  for b in range(a+1,n*n):
   Z=units[a]*s.diag(*w)*units[b]-units[b]*s.diag(*w)*units[a]
   cols.append(s.Matrix(n*n,1,[Z[i,j] for i in range(n) for j in range(n)]))
 L=s.Matrix.hstack(*cols);G=L*L.T;S=sum(x*x for x in w)
 v=s.Matrix([w[i] if i==j else 0 for i in range(n) for j in range(n)])
 expected=S*s.eye(n*n)-v*v.T
 assert G==expected
 checks.append(dict(weights=w,full_exterior_norm_sq=S,gram_identity=True,eigenvalues={str(k):v for k,v in G.eigenvals().items()}))
a,b,w1,w2,w3=s.symbols('a b w1 w2 w3',real=True)
X=E(3,0,1)+a*E(3,0,2);Y=E(3,1,0)+b*E(3,2,0);W=s.diag(w1,w2,w3)
T=X*W*Y-Y*W*X;defect=(w1*w1+w2*w2)*sq(X)*sq(Y)-sq(T)
corrected=(w2*a-w3*b)**2+(w2*w2-w3*w3)*(b*b+a*a*b*b)
assert s.expand(defect-corrected)==0
result=dict(n2_identity_counterexample=example_n2,rank_one_sos_counterexample=example_sos,full_exterior_gram_checks=checks,first_sparse_family_corrected=True,scope='exact integer/symbolic diagnostics, no full decomposable-wedge proof')
assert example_n2['T_sq']!=example_n2['claimed_rhs'] and example_sos['actual_defect']!=example_sos['claimed_sos']
Path(__file__).with_name('independent-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
