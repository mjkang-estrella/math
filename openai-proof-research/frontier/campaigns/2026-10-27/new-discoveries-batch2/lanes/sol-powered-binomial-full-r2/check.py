import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
from math import comb
from fractions import Fraction as F
from pathlib import Path
import json
C=lambda n,i:comb(n,i) if 0<=i<=n else 0
D=lambda r,l,a:sum((C(r,i)*a**i)**l for i in range(r+1))
def groups(r,j):return [[s*C(t,i)*C(u,j-i) for i in range(r+3)] for s,t,u in [(r+2,r,r+2),(r+1,r,r+1),(r+2,r,r+1),(r+1,r+1,r+1)]]
def top(v,k):return sum(sorted(v,reverse=True)[:k])
def interval(v,k):return max(sum(v[t:t+k]) for t in range(len(v)-k+1))
counts=dict(cleared_E=0,coefficients=0,source_identities=0,intervals=0,unions=0)
for r in range(13):
 for l in (1,2,3,4,5,8,12):
  for a in (F(1,10),F(1,2),F(1),F(3)):
   b,c,d=[D(t,l,a) for t in (r,r+1,r+2)]
   E=(r+2)**l*b*d-((r+2)**l-(r+1)**l)*b*c-(r+1)**l*c*c
   assert E==b*c*((r+2)**l*(d/c-1)-(r+1)**l*(c/b-1))
   expanded=0
   for j in range(2*r+3):
    p1,p2,n1,n2=groups(r,j)
    coef=sum(t**l for t in p1+p2)-sum(t**l for t in n1+n2)
    expanded+=coef*a**(l*j)
    assert coef>=0
    counts['coefficients']+=1
   assert expanded==E
   if l==1:assert E==a*(1+a)**(2*r+1)
   counts['cleared_E']+=1
for m in range(2,25):
 for l in (1,2,3,5,12):
  for a in (F(1,10),F(1),F(7)):
   prevQ=F(0);prevW=F(0)
   for r in range(m):
    u=(C(m,r+1)*a**(r+1))**l
    N=sum((C(m,i)*a**i)**l for i in range(r+1))
    Q=N/u;rho=(F(r+1,1)/(a*(m-r)))**l
    assert Q==rho*(1+prevQ)
    W=Q/(r+1)**l
    assert W>prevW
    A=(r+1)**l*(D(r+1,l,a)/D(r,l,a)-1)
    assert (N+u)/D(r+1,l,a)-N/D(r,l,a)==u/D(r+1,l,a)*(1-A*W)
    prevQ=Q;prevW=W;counts['source_identities']+=1
for r in range(13):
 for j in range(2*r+3):
  g=groups(r,j)
  for v in g:
   v=[t*t for t in v]
   for k in range(len(v)+1):assert top(v,k)==interval(v,k);counts['intervals']+=1
  for a,b in [(g[0],g[1]),(g[2],g[3])]:
   a=[t*t for t in a];b=[t*t for t in b]
   for k in range(len(a)+len(b)+1):
    assert top(a+b,k)==max(interval(a,h)+interval(b,k-h) for h in range(max(0,k-len(b)),min(k,len(a))+1));counts['unions']+=1
# Strictly positive interior obstructions to the two shortcut matchings.
g=groups(2,4);assert [v[2] for v in g]==[24,9,12,27]
assert 24**2+9**2-12**2-27**2==-216
s=[sorted(v,reverse=True) for v in groups(2,1)]
assert [v[1] for v in s]==[8,6,8,9]
assert 8**2+6**2-8**2-9**2==-45
out={'status':'PASS_FINITE_DIAGNOSTICS_ONLY','counts':counts,'same_index_obstruction':{'r':2,'j':4,'i':2,'P':[24,9],'N':[12,27],'square_gap':-216},'same_rank_obstruction':{'r':2,'j':1,'rank_zero_based':1,'P':[8,6],'N':[8,9],'square_gap':-45},'memory_bytes':536870912,'cpu_seconds':30,'threads':1,'source_proof':False}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
