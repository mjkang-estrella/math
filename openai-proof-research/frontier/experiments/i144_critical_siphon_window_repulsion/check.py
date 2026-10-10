"""New finite exact checks. No integration, inherited diagnostics, or universal certification."""
from fractions import Fraction as F
from itertools import combinations, product

def sets(n):
 for r in range(1,n):
  for z in combinations(range(n),r):yield frozenset(z)
def siphon(z,edges):
 return all(not any(v[i] for i in z) or any(u[i] for i in z) for u,v in edges)
def paths(z,edges):
 arcs={j:set() for j in z};marked=set()
 for u,v in edges:
  if sum(u[i] for i in z)!=1:continue
  j=next(i for i in z if u[i])
  arcs[j].update(i for i in z if i!=j and v[i])
  if sum(v[i] for i in z)>=2:marked.add(j)
 out={}
 for j in sorted(z):
  queue=[(j,)];seen={j}
  while queue:
   p=queue.pop(0)
   if p[-1] in marked:out[j]=p;break
   for i in sorted(arcs[p[-1]]-seen):seen.add(i);queue.append(p+(i,))
  assert j in out and len(out[j])<=len(z)
 return out

def run():
 counts={};ys=[(2,1,0),(1,2,0),(0,2,1),(0,1,2),(1,0,2),(2,0,1)]
 cycle=[(ys[i],ys[(i+1)%6]) for i in range(6)]
 ring=cycle+[(v,u) for u,v in cycle]
 ledger=[]
 for rare in sets(3):
  if not siphon(rare,ring):continue
  for u,v in ring:
   p=sum(u[i] for i in rare);b=sum(v[i]-u[i] for i in rare)
   assert b>=0 or p>=2
   ledger.append((tuple(sorted(rare)),u,v,p,b))
  assert len([1 for u,v in ring if sum(v[i]-u[i] for i in rare)<0])==4
 counts['ring_harmful_rare_order_rows']=len(ledger)
 # Exact polynomial identity: w^2 - [(1-w)(B^2+C^2)+BCw] = 2BC+w(B^2-BC+C^2).
 # Check coefficients by multiplying sparse polynomials, not sampled floats.
 def mul(p,q):
  out={}
  for (i,j),a in p.items():
   for (k,l),b in q.items():out[i+k,j+l]=out.get((i+k,j+l),0)+a*b
  return out
 w={(1,0):1,(0,1):1};w2=mul(w,w)
 harm=mul({(0,0):1,(1,0):-1,(0,1):-1},{(2,0):1,(0,2):1})
 for k,v in mul({(1,1):1},w).items():harm[k]=harm.get(k,0)+v
 diff={k:w2.get(k,0)-harm.get(k,0) for k in set(w2)|set(harm)}
 rhs=mul(w,{(2,0):1,(1,1):-1,(0,2):1});rhs[1,1]=2
 assert {k:v for k,v in diff.items() if v}=={k:v for k,v in rhs.items() if v}
 # B^2-BC+C^2=(B-C)^2+BC, hence nonnegative.
 counts['exact_harmful_polynomial_identity']=1
 receipts=[]
 for name,edges in [('bidirectional',ring),('one_direction',cycle)]:
  zs=[z for z in sets(3) if siphon(z,edges)]
  assert zs==[frozenset(z) for z in combinations(range(3),2)]
  for z in zs:receipts.append(dict(graph=name,z=sorted(z),paths={str(j):list(p) for j,p in paths(z,edges).items()}))
 assert any(len(p)>1 for r in receipts if r['graph']=='one_direction' for p in r['paths'].values())
 counts['ring_siphon_transfer_checks']=len(receipts)
 family=0
 for n in range(3,7):
  complexes=[]
  for i in range(n):
   for j in range(n):
    if i!=j:
     u=[0]*n;u[i]=2;u[j]=1;complexes.append(tuple(u))
  edges=[(u,v) for u in complexes for v in complexes if u!=v]
  for z in sets(n):
   sy=siphon(z,edges);assert sy==(len(z)==n-1)
   if sy:paths(z,edges)
   family+=1
 counts['higher_rank_family_faces']=family
 # Return budget with E representing exp(DH), E>=1. rho<=G/(8DHE^2).
 budget=0
 for D,H,G,E in product([F(1),F(3)],[F(1,7),F(2)],[F(1,11),F(4)],[F(1),F(3),F(20)]):
  rho=min(F(1,2),G/(8*D*H*E*E));u=rho*F(3,7)
  loss=4*D*H*E*E*u*u
  assert loss<=G*u/2
  q=min(F(1),G/2);assert G*u-loss>=q*u
  budget+=1
 counts['exact_return_budget_instances']=budget
 # Every shifted full-period pulse integral, split across at most two copies.
 T=F(1,100);ell=T/12;sliding=0
 for e in range(12):
  for s in [j*ell/7 for j in range(169)]:
   integral=sum(max(F(0),min(s+T,(p*12+e+1)*ell)-max(s,(p*12+e)*ell)) for p in range(5))
   assert integral==ell;sliding+=1
 counts['small_period_sliding_integrals']=sliding
 assert F(1)/(1-12*T)==F(25,22)<2
 # First-slot physical ODE with symbolic exponential variable u: A=a,B=b*u,C=eps-b*u.
 for eps,u in product([F(1,10),F(1,100),F(1,1000)],[F(1),F(9,10)]):
  a=1-eps;b=eps-eps**3;B=b*u;C=eps-B
  flux=a*a*B;Bp=-b*a*a*u;Cp=-Bp
  assert B+C==eps and Bp==-flux and Cp==flux and Bp+Cp==0 and a+B+C==1
 counts['exact_first_slot_state_identities']=6
 # Endpoint active-affine support has >= orientation, including ties.
 for x,z in product([F(-2),F(0),F(1,2),F(2)],repeat=2):
  branches=[(F(1),F(0)),(F(-1),F(1)),(F(0),F(1,2))]
  f=lambda t:min(r*t+b for r,b in branches)
  for r,b in branches:
   if r*z+b==f(z):assert f(z)-f(x)>=r*(z-x)
 counts['endpoint_support_instances']=16
 return dict(status='PASS',counts=counts,transfer_paths=receipts,scope='Finite exact structures and budgets only; no universal dynamics, numerical integration, contribution or P138 certification')

if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
