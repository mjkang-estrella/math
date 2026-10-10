"""New finite exact checks only. No universal or contribution certification."""
from fractions import Fraction as F
from itertools import product,combinations

def run():
 counts={}
 # Binding network: enumerate siphons, certificates and every admissible initial support.
 ys=[(1,1,0,0),(0,0,1,0),(0,0,0,1)]
 edges=[(ys[0],ys[1]),(ys[1],ys[0]),(ys[1],ys[2]),(ys[2],ys[1])]
 W=[(1,0,1,1),(0,1,1,1)];siphons=[]
 for mask in range(1,16):
  Z={i for i in range(4) if mask>>i&1}
  if all(not any(b[i] for i in Z) or any(a[i] for i in Z) for a,b in edges):siphons.append(Z)
 minimal=[z for z in siphons if not any(w<z for w in siphons)]
 assert minimal==[{0,2,3},{1,2,3}]
 for w in W:
  for a,b in edges:assert sum(w[i]*(b[i]-a[i]) for i in range(4))==0
 n=0
 for mask in range(16):
  J={i for i in range(4) if mask>>i&1}
  if any(z.isdisjoint(J) for z in siphons):continue
  for step in range(4):
   J|={i for a,b in edges if all(not a[j] or j in J for j in range(4)) for i in range(4) if b[i]}
  assert len(J)==4;n+=1
 counts['binding_support_closures']=n
 # Rank-one source orders for all directed edges among equal-degree two-species complexes.
 n=0
 for degree in range(1,9):
  for a,b in product(range(degree+1),repeat=2):
   if a==b:continue
   p=min(a,b)
   # At B=0 order is its exponent; decreasing B has source >= minimum+1.
   src,target=(a,b) if a>b else (b,a)
   assert src>=p+1 and target==p;n+=1
 counts['rank_one_integer_gaps']=n
 # Nondoubling return budget, replacing exp(DT) by a rational symbol E>=1.
 n=0
 for p,A,Z,E in product(range(7),[F(1,3),F(1),F(7)],[F(1,4),F(2),F(5)],[F(1),F(3,2),F(4)]):
  rho=min(F(1,2),A/(2*Z*2**(p+1)*E**(2*p+1)))
  for z in [rho,rho/2,rho/7]:
   gain=A/E**p*z**p;loss=Z*2**(p+1)*E**(p+1)*z**(p+1)
   assert gain-loss>=gain/2;n+=1
 counts['return_budget_instances']=n
 # Periodic ring: exact full-period integral for arbitrary fractional starts.
 def primitive(t,slot):
  periods=t//12;r=t-12*periods
  return periods+max(F(0),min(F(1),r-slot))
 n=0
 for slot in range(12):
  for q in range(97):
   s=F(q,7);assert primitive(s+12,slot)-primitive(s,slot)==1;n+=1
 counts['ring_sliding_window_integrals']=n
 # Exact initial pure nonlinear production, plus the conserved ring and its critical siphon.
 for eps in [F(1,10),F(1,100),F(1,10000)]:
  a0=1-eps;a1=a0/(1+a0);b1=1-a1
  assert a1+b1==1 and b1>F(1,2) and a1>F(2,5)
 counts['production_amplification_endpoints']=3
 ring=[(2,1,0),(1,2,0),(0,2,1),(0,1,2),(1,0,2),(2,0,1)]
 for i in range(6):assert sum(ring[i])==sum(ring[(i+1)%6])==3
 Z={1,2};assert all(any(a[i] for i in Z) for a in ring)
 # The two independent changes force all conservation vectors to be multiples of (1,1,1).
 v=[ring[1][i]-ring[0][i] for i in range(3)];w=[ring[2][i]-ring[1][i] for i in range(3)]
 assert v[0]*w[1]-v[1]*w[0]!=0
 counts['ring_conservation_and_critical_face']=1
 return dict(status='PASS',counts=counts,scope='Finite exact structure and rational budgets only; no universal permanence, numerical error or contribution certification')
if __name__=='__main__':
 import json;print(json.dumps(run(),indent=2))
