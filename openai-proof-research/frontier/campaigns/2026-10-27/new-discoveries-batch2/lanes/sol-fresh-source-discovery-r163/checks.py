import json,random,math
from pathlib import Path
L=Path(__file__).resolve().parent
def trim(a):
 while len(a)>1 and not a[-1]:a.pop()
 return a
def add(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)
def pmul(a,b):
 c=[[0] for _ in range(len(a)+len(b)-1)]
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=add(c[i+j],mul(x,y))
 return c
def extrema(p,n,a,kind):
 scores=[]
 for i,c in enumerate(p):
  if not any(c):continue
  v=-(len(c)-1) if kind=='degree' else next(j for j,x in enumerate(c) if x)
  scores.append((n*v+i*a,i))
 w=min(x for x,i in scores);idx=[i for x,i in scores if x==w]
 return w,min(idx),max(idx)
r=random.Random(163);counts={}
for kind in ['degree','codegree']:
 count=0
 for _ in range(1200):
  p=[trim([r.randint(-2,2) for _ in range(r.randint(1,7))]) for i in range(r.randint(1,8))]
  q=[trim([r.randint(-2,2) for _ in range(r.randint(1,7))]) for i in range(r.randint(1,8))]
  if not any(any(c) for c in p) or not any(any(c) for c in q):continue
  n=r.randint(2,19);a=r.randint(-20,20)
  ep,eq,ef=extrema(p,n,a,kind),extrema(q,n,a,kind),extrema(pmul(p,q),n,a,kind)
  assert ef==tuple(x+y for x,y in zip(ep,eq));count+=1
 counts[kind]=count
lattice=0
for n in range(2,81):
 for m in range(1,61):
  if math.gcd(n,m)!=1:continue
  for a in [m,-m]:
   assert all((s*a)%n for s in range(1,n));lattice+=1
assert pmul([[0,-1],[0],[1]],[[0,1],[0],[1]])==[[0,0,-1],[0],[0],[0],[1]]
# Rational half-degree trap: X^2-t^2 with omega=degree/2.
assert pmul([[0,-1],[1]],[[0,1],[1]])==[[0,0,-1],[0],[1]]
# Cancellation tied minima away from extremes is harmless.
assert extrema(pmul([[1],[1]],[[1],[-1]]),2,0,'codegree')==(0,0,2)
out=dict(seed=163,weighted_extrema_products=counts,coprime_signed_lattice_controls=lattice,gcd_and_rational_value_traps=2,cancellation_control=1,status='PASS',scope='Finite controls only; universal proof is PROOF.md')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
