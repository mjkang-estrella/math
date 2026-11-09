"""Bounded independent exact identity check, not a universal proof."""
from pathlib import Path
from fractions import Fraction as F
import itertools, json, resource, time
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2))
t=time.monotonic();counts={}
for n in range(2,5):
 arcs=[(i,j) for i in range(n) for j in range(n) if i!=j]
 c=dict(inputs=2**len(arcs),balanced=0,irregular=0,regular_scalar=0,regular_nonscalar=0,pair_checks=0)
 for bits in itertools.product(range(2),repeat=len(arcs)):
  A=[[0]*n for _ in range(n)]
  for (i,j),a in zip(arcs,bits): A[i][j]=a
  d=list(map(sum,A))
  if any(d[i]!=sum(A[j][i] for j in range(n)) for i in range(n)):continue
  c['balanced']+=1
  C=[[A[i][j]+A[j][i] for j in range(n)] for i in range(n)]
  H=[[F(d[i]*(i==j))-F(C[i][j],2) for j in range(n)] for i in range(n)]
  assert all(sum(row)==0 for row in H)
  for i in range(n):
   x=[F(k==i)-F(1,n) for k in range(n)]
   assert sum(x)==0 and sum(a*a for a in x)==F(n-1,n)
   assert sum(x[k]*H[k][l]*x[l] for k in range(n) for l in range(n))==d[i]
  if len(set(d))>1:
   c['irregular']+=1
   assert F(n,n-1)*(max(d)-min(d))>1
   continue
  if len({C[i][j] for i,j in arcs})==1:
   c['regular_scalar']+=1;continue
  c['regular_nonscalar']+=1;found=False
  for i,j in itertools.combinations(range(n),2):
   v=[C[k][i]-C[k][j] if k not in [i,j] else 0 for k in range(n)]
   if not any(v):continue
   found=True;c['pair_checks']+=1
   w=[int(k==i)-int(k==j) for k in range(n)];s=sum(a*a for a in v)
   assert sum(v)==0 and s>=2 and sum(w[k]*v[k] for k in range(n))==0
   cw=[sum(C[k][l]*w[l] for l in range(n)) for k in range(n)]
   assert cw==[v[k]-C[i][j]*w[k] for k in range(n)]
   assert sum(w[k]*H[k][l]*v[l] for k in range(n) for l in range(n))==-F(s,2)
  assert found
 counts[n]=c
r=dict(counts=counts,seconds=time.monotonic()-t,arithmetic='integer and Fraction only',limits='all labeled loopless digraphs n=2..4; CPU 20s, address space 256MiB',status='PASS',scope='identity and quantifier sanity checks; no spectral numerics; not universality evidence')
Path(__file__).with_name('diagnostic.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
