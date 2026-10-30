from pathlib import Path
from itertools import combinations,product
from fractions import Fraction as F
import json
L=Path(__file__).resolve().parent
def poly(n,edges):
 out=[0]*(len(edges)+1)
 for mask in range(1<<len(edges)):
  adj=[set() for _ in range(n)]
  for i,(u,v) in enumerate(edges):
   if mask>>i&1:adj[u].add(v);adj[v].add(u)
  ok=1 in adj[0] or bool(adj[0]&adj[1]) or any(adj[u]&adj[1] for u in adj[0])
  if ok:out[mask.bit_count()]+=1
 return out
def h(n,m):
 k=(m-1)//2
 e=[(0,1)]+[(u,v) for v in range(2,k+2) for u in [0,1]]
 if m%2==0:e.append((2,3))
 return e
def evalp(c,p):return sum(F(v)*p**i*(1-p)**(len(c)-1-i) for i,v in enumerate(c))
def state_failure(n,edges,p):
 # Exact conditional enumeration of terminal-edge states, integrating interior edges.
 terminal=[(u,v) for u,v in edges if u<2 or v<2];core=[(u,v) for u,v in edges if u>=2 and v>=2]
 ans=F(0)
 for mask in range(1<<len(terminal)):
  ss=set();tt=set();w=p**mask.bit_count()*(1-p)**(len(terminal)-mask.bit_count());direct=False
  for i,(u,v) in enumerate(terminal):
   if mask>>i&1:
    if (u,v)==(0,1):direct=True
    elif u==0:ss.add(v)
    elif u==1:tt.add(v)
  if direct or ss&tt:continue
  cross=sum((u in ss and v in tt) or (v in ss and u in tt) for u,v in core)
  ans+=w*(1-p)**cross
 return ans
results=[]
for n in range(2,7):
 es=list(combinations(range(n),2));M=len(es);size=1<<M
 # Independent BFS-like path predicate, followed by cardinality subset-zeta transform.
 counts=[[0]*size for _ in range(M+1)]
 for mask in range(size):
  nei=[0]*n
  for i,(u,v) in enumerate(es):
   if mask>>i&1:nei[u]|=1<<v;nei[v]|=1<<u
  reach=1
  for t in range(3):
   new=reach
   for v in range(n):
    if reach>>v&1:new|=nei[v]
   reach=new
  if reach&2:counts[mask.bit_count()][mask]=1
 for row in counts:
  for i in range(M):
   bit=1<<i
   for start in range(0,size,bit*2):
    for mask in range(start+bit,start+2*bit):row[mask]+=row[mask-bit]
 tested=0;violations=[];strict=0
 hpolys={m:poly(n,h(n,m)) for m in range(5,2*n-2)}
 for mask in range(size):
  m=mask.bit_count()
  if m<5 or m>2*n-3:continue
  cp=[row[mask] for row in counts[:m+1]];hp=hpolys[m]
  if any(a<b for a,b in zip(hp,cp)):violations.append(dict(mask=mask,counts=cp,H=hp))
  if hp!=cp:strict+=1
  tested+=1
 results.append(dict(n=n,tested=tested,coefficientwise_violations=violations[:3],violation_count=len(violations),strict=strict))
 assert not violations
 # Direct edge-subset enumerator independently controls selected cases and state integration.
 for mask in [size-1,size//3,size//5]:
  e=[v for i,v in enumerate(es) if mask>>i&1];cp=poly(n,e)
  assert cp==[row[mask] for row in counts[:len(e)+1]]
  for p in [F(1,3),F(1,2),F(2,3)]:assert state_failure(n,e,p)==1-evalp(cp,p)
# Closed H formula, odd and even, arbitrary-p rational controls.
controls=0
for n in range(5,9):
 for m in range(5,min(2*n-3,11)+1):
  e=h(n,m);k=(m-1)//2;cp=poly(n,e)
  for p in [F(1,4),F(1,3),F(1,2),F(2,3),F(3,4)]:
   q=1-p*p;rho=1-p
   expected=rho*q**k if m%2 else rho*(q**k-2*p**3*rho**2*q**(k-2))
   assert expected==state_failure(n,e,p)==1-evalp(cp,p);controls+=1
# Source's invalid deletion recurrence, exact witness.
e=h(8,10);e.remove((0,2));a=evalp(poly(8,e),F(1,2));b=evalp(poly(8,h(8,9)),F(1,2));assert a!=b
out=dict(status='PASS; bounded diagnostics only',all_labeled_graphs=results,state_controls=45,H_formula_controls=controls,deletion_witness=dict(n=8,m=10,removed=[0,2],deleted_R=str(a),H9_R=str(b)),limit='No all-order pathset injection or universal inequality proved')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
