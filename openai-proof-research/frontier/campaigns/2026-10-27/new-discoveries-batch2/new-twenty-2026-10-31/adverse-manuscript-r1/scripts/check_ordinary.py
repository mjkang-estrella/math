from pathlib import Path
from fractions import Fraction as F
import json,itertools,hashlib
R=Path(__file__).resolve().parents[1];c=json.loads((R/'inputs/outputs/latin36-certificate.json').read_text())
P=list(itertools.product(range(6),repeat=2))
def adj(p,q):return p!=q and (p[0]==q[0] or p[1]==q[1] or sum(p)%6==sum(q)%6)
B=[[int(p[0]==l if l<6 else p[1]==l-6 if l<12 else sum(p)%6==l-12) for p in P] for l in range(18)]
assert all(sum(B[l][i]*B[l][j] for l in range(18))==int(adj(p,q))+3*(p==q) for i,p in enumerate(P) for j,q in enumerate(P))
x=list(map(F,c['fractional_transversal']));z=list(map(F,c['eigenvector']))
for v in P:
 inds=[P.index(((p[0]-v[0])%6,(p[1]-v[1])%6)) for p in P]
 X=[x[i] for i in inds];Z=[z[i] for i in inds];S=[i for i,p in enumerate(P) if not adj(v,p)]
 assert len(S)==21 and any(Z) and all(t>=0 for t in X)
 assert all(X[i]==Z[i]==0 for i,p in enumerate(P) if adj(v,p))
 assert all(sum(row[i]*X[i] for i in range(36))==1 for row in B)
 assert all(sum(row[i]*Z[i] for i in range(36))==0 for row in B)
 simple=[F(0) if adj(v,p) else F(1) if p==v else F(1,4) for p in P]
 assert all(sum(row[i]*simple[i] for i in range(36))==1 for row in B)
 assert all(sum(int(adj(P[i],P[j]))*Z[j] for j in S)==-3*Z[i] for i in S)
w=[(0,0),(1,1),(2,2),(3,4),(4,5)]
assert all(not adj(a,b) for a,b in itertools.combinations(w,2))
assert all(len({(i+p[i])%6 for i in range(6)})<6 for p in itertools.permutations(range(6)))
(R/'receipts/ordinary-check.json').write_text(json.dumps({'status':'PASS','gram_entries':1296,'translated_deletions':36,'fractional_witnesses':'inherited and simplified','permutations_rejecting_six':720,'alpha':5,'upsilon':6,'least_eigenvalue':-3},indent=2)+'\n')
print('ordinary exact arithmetic PASS')
