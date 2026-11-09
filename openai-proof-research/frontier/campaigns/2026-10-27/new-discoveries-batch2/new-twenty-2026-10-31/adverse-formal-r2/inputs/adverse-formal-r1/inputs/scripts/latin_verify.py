from pathlib import Path
from fractions import Fraction as F
import itertools,json,hashlib,sys
D=Path(__file__).resolve().parents[1];r=json.loads((D/'outputs/latin36-certificate.json').read_text());P=list(itertools.product(range(6),repeat=2));N=36
line=lambda l,p: p[0]==l if l<6 else p[1]==l-6 if l<12 else sum(p)%6==l-12
adj=lambda p,q:p!=q and (p[0]==q[0] or p[1]==q[1] or sum(p)%6==sum(q)%6)
B=[[int(line(l,p)) for p in P] for l in range(18)];A=[[int(adj(p,q)) for q in P] for p in P]
assert all(sum(B[l][i]*B[l][j] for l in range(18))==A[i][j]+3*(i==j) for i in range(N) for j in range(N))
x=list(map(F,r['fractional_transversal']));z=list(map(F,r['eigenvector']));checks=[]
for base in P:
 tr=lambda p:((p[0]-base[0])%6,(p[1]-base[1])%6)
 X=[x[P.index(tr(p))] for p in P];Z=[z[P.index(tr(p))] for p in P];keep=[i for i,p in enumerate(P) if not adj(base,p)]
 assert all(v>=0 for v in X) and any(Z)
 assert all(X[i]==Z[i]==0 for i in range(N) if i not in keep)
 assert all(sum(B[l][i]*X[i] for i in range(N))==1 for l in range(18))
 assert all(sum(B[l][i]*Z[i] for i in range(N))==0 for l in range(18))
 assert all(sum(A[i][j]*Z[j] for j in keep)==-3*Z[i] for i in keep)
 obj=2*sum(X)-sum(X[i]*A[i][j]*X[j]/3 for i in keep for j in keep)-sum(X[i]**2 for i in keep)
 assert obj==6;checks.append({'base':base,'remaining':len(keep),'objective':str(obj),'eigenvalue':-3})
trans=[p for p in itertools.permutations(range(6)) if len({(i+p[i])%6 for i in range(6)})==6];assert not trans
# 5-cell witness; exhaustive among maps of first5 rows, stop first valid.
witness=next([(i,p[i]) for i in range(5)] for p in itertools.permutations(range(6),5) if len({(i+p[i])%6 for i in range(5)})==5)
assert all(not adj(a,b) for a,b in itertools.combinations(witness,2))
out={'method':'exact Fraction arithmetic, no floating tolerance','incidence_entries_checked':N*N,'neighborhood_checks':checks,'six_transversals':len(trans),'permutations_examined':720,'independent5':witness,'alpha':5,'quadratic_bound':6,'least_eigenvalue':-3,'formal_status':'ordinary certificate only; no kernel endpoint or acceptance'}
(D/'outputs/latin36-verified.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
