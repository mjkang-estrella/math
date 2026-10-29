"""Exact bounded diagnostics, not a proof of any universal conjecture."""
import os
for k in ['OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS']:os.environ[k]='1'
import resource,signal,random,json,itertools
from fractions import Fraction as F
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(30)
def solve(A,b):
 A=[[F(x) for x in r]+[F(y)] for r,y in zip(A,b)];n=len(b)
 for j in range(n):
  p=next((i for i in range(j,n) if A[i][j]),None)
  if p is None:return None
  A[j],A[p]=A[p],A[j];z=A[j][j];A[j]=[v/z for v in A[j]]
  for i in range(n):
   if i!=j:
    z=A[i][j];A[i]=[x-z*y for x,y in zip(A[i],A[j])]
 return [r[-1] for r in A]
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def profile(rows):
 n=len(rows);d=3
 assert all(sum(r[j] for r in rows)==0 for j in range(d))
 M=[[sum(F(r[i]*r[j],n) for r in rows) for j in range(d)] for i in range(d)]
 def inner(u,v):return sum(u[i]*M[i][j]*v[j] for i in range(d) for j in range(d))
 bases={s:solve([rows[i] for i in s],[1]*d) for s in itertools.combinations(range(n),d)}
 bases={s:q for s,q in bases.items() if q is not None}
 x=min(inner(q,q) for q in bases.values());y=x;faces=0
 for T in itertools.combinations(range(n),d+1):
  Q=[bases[s] for s in itertools.combinations(T,d) if s in bases]
  for size in range(1,len(Q)+1):
   for I in itertools.combinations(range(len(Q)),size):
    P=[Q[i] for i in I];G=[[inner(p,q) for q in P] for p in P]
    A=[r+[F(1)] for r in G]+[[F(1)]*size+[F(0)]]
    z=solve(A,[F(0)]*size+[F(1)])
    if z is None or min(z[:size])<0:continue
    u=[sum(z[i]*P[i][j] for i in range(size)) for j in range(d)]
    val=inner(u,u);assert val>=0;y=min(y,val);faces+=1
 return dict(rows=rows,x=str(x),y=str(y),facet=str(2*x+3*y),facet_pass=2*x+3*y<=6,bases=len(bases),faces=faces)
def partitions(n,m,lo=1):
 if m==1:
  if n>=lo:yield(n,)
 else:
  for a in range(lo,n//m+1):
   for t in partitions(n-a,m-1,a):yield(a,)+t
def gamma(d,k):
 return max(F(s-k,1)/min(sum((F(1,r) for r in p),F(0)) for p in partitions(d,s)) for s in range(k+1,d+1))
checks=[]
for d in range(2,13):
 for k in range(1,d):
  exact=gamma(d,k);balanced=max(F(s-k,1)/(F(s-d%s,d//s)+F(d%s,d//s+1)) for s in range(k+1,d+1));assert exact==balanced
  checks.append([d,k,str(exact)])
rows=[(1,0,0),(0,1,0),(0,0,1),(-1,-1,-1)]
examples=[profile(rows),profile([(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)])]
rng=random.Random(241029)
for _ in range(24):
 a=[tuple(rng.randint(-3,3) for j in range(3)) for i in range(4)]
 a.append(tuple(-sum(r[j] for r in a) for j in range(3)))
 if any(not any(r) for r in a):continue
 try:examples.append(profile(a))
 except ValueError:continue
assert examples[0]['x']=='3' and examples[0]['y']=='0'
assert examples[1]['x']=='1' and examples[1]['y']=='2/3'
assert all(e['facet_pass'] for e in examples)
# Independent weighted normal equation identity on a generic four-point support.
R=[(1,0,0),(0,1,0),(0,0,1),(-1,-1,-1)];alpha=[F(1),F(2),F(3),F(4)]
H=[[sum(alpha[a]*R[a][i]*R[a][j] for a in range(4)) for j in range(3)] for i in range(3)]
b=[sum(alpha[a]*R[a][j] for a in range(4)) for j in range(3)];u=solve(H,b)
Q=[solve([R[a] for a in range(4) if a!=i],[1]*3) for i in range(4)]
l=[1/a for a in alpha];l=[v/sum(l) for v in l];v=[sum(l[a]*Q[a][j] for a in range(4)) for j in range(3)];assert u==v
out=dict(status='PASS_DIAGNOSTICS_ONLY',seed=241029,partition_checks=checks,profiles=examples,weighted_identity=list(map(str,u)),limits=dict(address_space_bytes=512*1024**2,cpu_seconds=25,wall_alarm_seconds=30,blas_threads=1))
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2));print('PASS',len(checks),'partition cells;',len(examples),'exact component profiles; weighted normal equation identity')
