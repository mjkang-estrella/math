"""Fixed 4x4/5x5 source checks and two-parameter identity, not target proof."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import sympy as s,json,itertools,datetime
from pathlib import Path
A=s.Matrix([[1,s.Rational(1,2),-1,-1],[s.Rational(1,3),1,-1,-1],[-1,-1,1,0],[-1,-1,0,1]])
B=s.Matrix([[1,0,0,-1,-1],[-1,2,0,0,-1],[-1,-s.Rational(1,2),1,0,0],[0,-1,-1,1,0],[0,-s.Rational(1,2),-s.Rational(1,2),-1,1]])
rows=[]
for M in (A,B):
 n=M.rows;classification={():True}
 for r in range(1,n+1):
  for ix in itertools.combinations(range(n),r):
   C=M.extract(ix,ix)
   if any(not classification[ix[:k]+ix[k+1:]] for k in range(r)):e0=False
   elif C.det()==0:e0=True # Non-E0 with E0 proper blocks would be almost E0, hence invertible.
   else:e0=not all(v<=0 for v in C.inv())
   classification[ix]=e0
 assert all(v for ix,v in classification.items() if len(ix)==n-2)
 assert all(not v for ix,v in classification.items() if len(ix)>=n-1)
 assert M.det()<0
 assert all(M.inv()[i,j]<=0 for i in range(n) for j in range(n) if i!=j)
 rows.append(dict(n=n,det=str(M.det()),principal_subsets=len(classification)-1,E02=True,inverse=[list(map(str,M.inv().row(i))) for i in range(n)]))
p,q=s.symbols('p q');M=s.Matrix([[1,p,-1,-1],[q,1,-1,-1],[-1,-1,1,0],[-1,-1,0,1]])
D=p*q-2*p-2*q+3
N=s.Matrix([[1,p-2,p-1,p-1],[q-2,1,q-1,q-1],[q-1,p-1,(p-1)*(q-1),p+q-2],[q-1,p-1,p+q-2,(p-1)*(q-1)]])
assert (M*N-D*s.eye(4)).applyfunc(s.expand)==s.zeros(4)
assert s.expand(M.det()+D)==0
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),known_source_examples=rows,parameter_inverse_identity=True,full_conjecture_proved=False,cap_bytes=512*1024**2)
Path(__file__).with_name('exact-checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
