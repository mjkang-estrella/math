#!/usr/bin/env python3
"""Exact bounded diagnostics only. No conjecture is inferred from a scan."""
import os,resource,json,time,itertools
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(90,90))
for v in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[v]='1'
from sympy.polys.rings import ring
from sympy import ZZ
from pathlib import Path
P=Path(__file__).parent
R,q=ring('q',ZZ)
def det(a):
 a=[r[:] for r in a];p=R.one;s=1;n=len(a)
 for k in range(n-1):
  if not a[k][k]:
   j=next((j for j in range(k+1,n) if a[j][k]),None)
   if j is None:return R.zero
   a[k],a[j]=a[j],a[k];s=-s
  pivot=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):a[i][j]=(a[i][j]*pivot-a[i][k]*a[k][j]).exquo(p)
   a[i][k]=R.zero
  p=pivot
 return s*a[-1][-1]
def block(n,k,w=None):
 h=n+k;w=list(range(h)) if w is None else w
 # B^k rows 0..n-1. Gram identity uses detailed balance d_j/d_i.
 a=[[R.one if i==j else R.zero for j in range(h)] for i in range(n)]
 for _ in range(2*k):
  a=[[sum((a[i][t] for t in range(max(0,j-1),min(h,j+2))),R.zero)*q**w[j] for j in range(h)] for i in range(n)]
 return det([row[:n] for row in a])
out={'limits':{'AS_bytes':512*1024**2,'CPU_seconds':90,'BLAS_threads':1},'even_checks':[]}
for k in range(1,9):
 for n in range(1,8):
  t=time.monotonic();f=block(n,k);neg=[(e[0],int(c)) for e,c in f.items() if c<0]
  out['even_checks'].append({'n':n,'k':k,'terms':len(f),'degree':f.degree(),'negative':neg[:10],'seconds':time.monotonic()-t})
  (P/'checks.json').write_text(json.dumps(out,indent=2))
  print(n,k,len(f),'NEG' if neg else 'ok',flush=True)
  if neg:raise SystemExit('COUNTEREXAMPLE')
# An independent-height specialization tests a proposed stronger invariant only.
for w in ([0,1,2,3,4,5],[0,0,1,0,0,0],[0,1,0,0,0,0],[0,1,4,2,3,0],[0,5,1,4,2,3]):
 f=block(3,3,w);neg=[(e[0],int(c)) for e,c in f.items() if c<0]
 out.setdefault('nongeometric',[]).append({'w':w,'negative':neg,'polynomial':str(f)})
(P/'checks.json').write_text(json.dumps(out,indent=2))
