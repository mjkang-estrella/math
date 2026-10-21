"""Exact finite diagnostics of the derived root interfaces, not source or theorem gates."""
from itertools import product
from pathlib import Path
import json,signal,random
signal.alarm(35)
OUT=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r125/notes/diagnostic.json')
class Ring:
 def __init__(self,p,v,w,beta):
  self.p,self.v,self.w,self.beta=p,v,w,beta;self.D=1+v+w
  self.zero=(0,)*self.D;self.one=(1,)+(0,)*(self.D-1)
 def add(self,x,y):return tuple((a+b)%self.p for a,b in zip(x,y))
 def mul(self,x,y):
  p=self.p;v=self.v;w=self.w
  return ((x[0]*y[0])%p,)+tuple((x[0]*y[1+i]+y[0]*x[1+i])%p for i in range(v))+tuple((x[0]*y[1+v+k]+y[0]*x[1+v+k]+sum(x[1+i]*y[1+j]*self.beta[i][j][k] for i in range(v) for j in range(v)))%p for k in range(w))
 def power(self,x,n):
  z=self.one
  while n:
   if n&1:z=self.mul(z,x)
   x=self.mul(x,x);n//=2
  return z
 def elements(self):return product(range(self.p),repeat=self.D)
 def basis(self):return [tuple(int(i==j) for i in range(self.D)) for j in range(self.D)]
def check_ring(R):
 bs=R.basis()
 assert all(R.mul(R.one,b)==b for b in bs)
 assert all(R.mul(a,b)==R.mul(b,a) for a in bs for b in bs)
 assert all(R.mul(R.mul(a,b),c)==R.mul(a,R.mul(b,c)) for a in bs for b in bs for c in bs)
 return len(bs)**3
records=[];rng=random.Random(125);assoc=0
for trial in range(6):
 v=w=2;p=3
 beta=[[[0]*w for j in range(v)] for i in range(v)]
 for i in range(v):
  for j in range(i,v):
   beta[i][j]=[rng.randrange(p) for _ in range(w)];beta[j][i]=beta[i][j][:]
 R=Ring(p,v,w,beta);assoc+=check_ring(R);els=list(R.elements())
 counts={a:0 for a in els}
 for x in els:counts[R.mul(x,x)]+=1
 for aw in product(range(p),repeat=w):
  a=(0,)+(0,)*v+aw
  qcount=sum(tuple(sum(z[i]*z[j]*beta[i][j][k] for i in range(v) for j in range(v))%p for k in range(w))==aw for z in product(range(p),repeat=v))
  assert counts[a]==p**w*qcount
 # Frobenius annihilates radical; coefficient core is exactly scalars.
 image={R.power(x,p) for x in els};assert image=={(c,)+(0,)*(v+w) for c in range(p)}
 for a in els:
  if not a[0]:continue
  assert counts[a]==(2 if a[0]==1 else 0)
  sixth=sum(R.power(x,6)==a for x in els if x[0])
  assert sixth==(2*p**(v+w) if a==R.one else 0)
 records.append({'kind':'graded-local','trial':trial,'dimension':R.D,'cardinality':len(els),'square-count-comparisons':p**w,'unit-square-and-sixth-power-targets':2*p**(v+w)})
# Construct beta from 3-CNF homogeneous quadrics, independently polarizing Q.
def sat_ring(n,clauses):
 v=1+n+len(clauses);w=1+n+2*len(clauses)
 def Q(z):
  t=z[0];xs=z[1:1+n];ys=z[1+n:]
  q=[t*t]+[x*x-t*x for x in xs]
  for literals,y in zip(clauses,ys):
   false=[t-xs[abs(l)-1] if l>0 else xs[abs(l)-1] for l in literals]
   q += [false[0]*false[1]-t*y,y*false[2]]
  return tuple(x%3 for x in q)
 bs=[tuple(int(i==j) for i in range(v)) for j in range(v)];qs=[Q(b) for b in bs]
 beta=[]
 for i in range(v):
  row=[]
  for j in range(v):
   q=Q(tuple(a+b for a,b in zip(bs[i],bs[j])))
   row.append([(2*(q[k]-qs[i][k]-qs[j][k]))%3 for k in range(w)])
  beta.append(row)
 return Ring(3,v,w,beta),Q
for clauses in [[(1,1,1)],[(1,-1,1)],[(1,1,1),(-1,-1,-1)]]:
 R,Q=sat_ring(1,clauses);assoc+=check_ring(R)
 a=(0,)+(0,)*R.v+(1,)+(0,)*(R.w-1)
 sat=sum(all(any((bits[abs(l)-1]==1 if l>0 else bits[abs(l)-1]==0) for l in cl) for cl in clauses) for bits in product(range(2),repeat=1))
 # Enumerate ALL V vectors; independently use actual multiplication on each.
 vc=0
 for z in product(range(3),repeat=R.v):
  x=(0,)+z+(0,)*R.w
  assert R.mul(x,x)[1+R.v:]==Q(z)
  vc+=R.mul(x,x)==a
 assert vc==2*sat
 # Full algebra enumeration in the first small example, including scalar and W coordinates.
 full=None
 if len(clauses)==1 and clauses[0]==(1,1,1):
  full=sum(R.mul(x,x)==a for x in R.elements());assert full==2*3**R.w*sat
 records.append({'kind':'3CNF','clauses':clauses,'dimension':R.D,'sat_count':sat,'V_solutions':vc,'W_free_dimension':R.w,'derived_root_count':vc*3**R.w,'full_enumeration_root_count':full})
# Square-zero singular-root test with arbitrary nilpotent polynomial coefficients.
R=Ring(3,2,0,[[[] for j in range(2)] for i in range(2)]);assoc+=check_ring(R)
els=list(R.elements())
def evaluate(cs,x):
 y=R.zero
 for c in reversed(cs):y=R.add(R.mul(y,x),c)
 return y
for trial in range(12):
 cs=[tuple(rng.randrange(3) for _ in range(R.D)) for j in range(4)]
 actual={x for x in els if evaluate(cs,x)==R.zero};pred=set()
 for r in range(3):
  base=(r,0,0);fr=evaluate(cs,base)
  deriv=sum(j*cs[j][0]*pow(r,j-1,3) for j in range(1,4))%3
  for j in product(range(3),repeat=2):
   t=(fr[0],(fr[1]+deriv*j[0])%3,(fr[2]+deriv*j[1])%3)
   if t==R.zero:pred.add((r,)+j)
 assert actual==pred
records.append({'kind':'square-zero','polynomials':12,'all_elements_per_polynomial':27})
OUT.write_text(json.dumps({'seed':125,'associativity_basis_triples':assoc,'records':records,'limits':'Exact finite diagnostics only; no universal correctness, source audit, contribution or acceptance gate.'},indent=2)+'\n')
print('Completed',len(records),'records;',assoc,'basis-triple associativity identities; all finite comparisons matched.')
