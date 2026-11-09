"""Exact input checks only. This is not a Lean proof or novelty clearance."""
from pathlib import Path
from fractions import Fraction as F
import json,itertools,sys

def check(r):
 P=list(itertools.product(range(6),repeat=2))
 def adj(p,q):return p!=q and (p[0]==q[0] or p[1]==q[1] or sum(p)%6==sum(q)%6)
 B=[[int(p[0]==l if l<6 else p[1]==l-6 if l<12 else sum(p)%6==l-12) for p in P] for l in range(18)]
 A=[[int(adj(p,q)) for q in P] for p in P]
 assert all(sum(B[l][i]*B[l][j] for l in range(18))==A[i][j]+3*(i==j) for i in range(36) for j in range(36))
 x=list(map(F,r['fractional_transversal']));z=list(map(F,r['eigenvector']))
 assert len(x)==len(z)==36
 for v in P:
  tr=lambda p:((p[0]-v[0])%6,(p[1]-v[1])%6)
  X=[x[P.index(tr(p))] for p in P];Z=[z[P.index(tr(p))] for p in P]
  keep=[i for i,p in enumerate(P) if not adj(v,p)]
  assert len(keep)==21 and any(Z) and all(t>=0 for t in X)
  assert all(X[i]==Z[i]==0 for i in range(36) if i not in keep)
  assert all(sum(B[l][i]*X[i] for i in range(36))==1 for l in range(18))
  assert all(sum(B[l][i]*Z[i] for i in range(36))==0 for l in range(18))
  assert all(sum(A[i][j]*Z[j] for j in keep)==-3*Z[i] for i in keep)
  assert 2*sum(X)-sum(X[i]*A[i][j]*X[j]/3 for i in keep for j in keep)-sum(X[i]**2 for i in keep)==6
 perms=list(itertools.permutations(range(6)))
 assert len(perms)==720 and all(len({(i+p[i])%6 for i in range(6)})<6 for p in perms)
 witness=[(0,0),(1,1),(2,2),(3,4),(4,5)]
 assert all(not adj(a,b) for a,b in itertools.combinations(witness,2))
 return {'incidence_entries':1296,'deletions':36,'remaining_vertices':21,'six_transversals':0,'permutations':720,'independent5':witness,'status':'exact arithmetic checks pass; no formal endpoint'}
if __name__=='__main__':
 p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'inputs/outputs/latin36-certificate.json'
 print(json.dumps(check(json.loads(p.read_text())),indent=2))
