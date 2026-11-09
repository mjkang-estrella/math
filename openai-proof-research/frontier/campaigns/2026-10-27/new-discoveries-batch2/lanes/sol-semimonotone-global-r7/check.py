"""Exact, fixed-size checks for the singular metric obstruction; no conjecture proof."""
import os,resource
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,)*2)
import sympy as s,json,itertools,datetime
from pathlib import Path
n=6; one=s.ones(n,1);J=s.eye(n)-one*one.T/n
D=s.Matrix(n,n,lambda i,j:0 if i==j else (1 if i//3==j//3 else s.Rational(3,5)))
assert all(D[i,j]<=D[i,k]+D[k,j] for i,j,k in itertools.product(range(n),repeat=3))
W=D.row_join(one).col_join(one.T.row_join(s.zeros(1)))
A=2*W.inv()[:n,:n]
assert A==s.Matrix(n,n,lambda i,j:s.Rational(1,3) if i==j else (s.Rational(7,3) if i//3==j//3 else -s.Rational(5,3)))
assert A.rank()==5 and A.det()==0 and A*one==s.zeros(n,1)
assert A.adjugate()==s.Rational(80,3)*s.ones(n)
assert all(A[i,i]>0 for i in range(n))
local=[]
for i in range(n):
 ids=[j for j in range(n) if j!=i];M=A.extract(ids,ids)
 C=s.Matrix(5,5,lambda j,k:-(D[ids[j],i]+D[i,ids[k]]-D[ids[j],ids[k]])/2)
 assert M*C==s.eye(5) and all(v<=0 for v in C)
 v=-C*s.ones(5,1)
 assert all(x>0 for x in v) and M*v==-s.ones(5,1)
 local.append({'deleted':i,'det':str(M.det()),'strict_nonE0_witness':list(map(str,v))})
# A principal four-block fails E0, with every witness coordinate positive.
ids=[0,1,3,4];H=A.extract(ids,ids)
assert H*s.ones(4,1)==-s.Rational(2,3)*s.ones(4,1)
assert A.extract([0,3],[0,3])*s.ones(2,1)==-s.Rational(4,3)*s.ones(2,1)
# General centered-distance identity checked on this exact fixture.
G=(A+one*one.T/n).inv()-one*one.T/n
assert A*G==J and G*one==s.zeros(n,1)
D2=s.Matrix(n,n,lambda i,j:2*G[i,j]-G[i,i]-G[j,j])
assert D2==D
# Nonsymmetric directed-semimetric parametrization, one exact fixture.
Q=s.Matrix(n,n,lambda i,j:0 if i==j else 10+(3*i+7*j)%11)
assert Q!=Q.T
assert all(Q[j,k]<=Q[j,i]+Q[i,k] for i,j,k in itertools.product(range(n),repeat=3))
GG=J*Q*J
AA=(GG+one*one.T/n).inv()-one*one.T/n
assert AA*GG==J and GG*AA==J
for i in range(n):
 ids=[j for j in range(n) if j!=i]
 CC=s.Matrix(n-1,n-1,lambda j,k:Q[ids[j],ids[k]]-Q[ids[j],i]-Q[i,ids[k]])
 assert AA.extract(ids,ids)*CC==s.eye(n-1) and all(v<=0 for v in CC)
# Replay both root's nonsingular countermodels without mutating its lane.
root=[]
for p,t,sgn in [(2,s.Integer(2),1),(3,s.Rational(3,5),-1)]:
 m=2*p;B=s.Matrix(m,m,lambda i,j:sgn*(1 if i==j else t*t if i//p==j//p else t));T=B.inv()
 assert all(T[i,i]>0 for i in range(m))
 for i in range(m):
  ids=[j for j in range(m) if i!=j]
  S=B.extract(ids,ids)-B.extract(ids,[i])*B.extract([i],ids)/B[i,i]
  assert all(x<=0 for x in S) and T.extract(ids,ids)*S==s.eye(m-1)
 assert T[0,0]+T[0,p]<0
 root.append({'n':m,'det':str(T.det()),'verified':True})
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'singular_metric_obstruction':{'A':[[str(x) for x in A.row(i)] for i in range(n)],'rank':5,'det':'0','cofactor':'80/3','maximal_blocks':local,'four_block_witness_image':'-2/3 ones','pair_witness_image':'-4/3 ones'},'root_fixtures':root,'metric_identity_verified':True,'full_conjecture_proved':False,'cap_bytes':512*1024**2,'cpu_seconds':35}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
