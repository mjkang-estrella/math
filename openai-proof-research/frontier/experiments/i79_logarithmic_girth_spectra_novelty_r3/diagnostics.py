"""Exact scope/bookkeeping checks, not analytic proof or novelty certificates."""
from fractions import Fraction as F
import json

def run():
 scale=[]
 for b in (2,3,6):
  for g in (3,4,8,16,32):
   n=b**(100*g);L=sum((F(b**r,2*r) for r in range(3,g+1)),F(0))
   assert L>=F(b**g,2*g) and L<=F(2*b,b-1)*F(b**g,g)
   assert F(b**(2*g-1),n)==F(1,b**(98*g+1))
   assert F(b**g,n)==F(1,b**(99*g))
   scale.append({'b':b,'g':g,'n_exact':'b^(100g)','Lambda_over_b_g_over_g':str(L*g/b**g),'MWW_ratio':'b^(-98g-1)','rejection_scale':'b^(-99g)'})
 pi=[F(1,20),F(9,20),F(1,4),F(1,4)]
 K=[[F(0),F(1),F(0),F(0)],[F(1,9),F(8,9),F(0),F(0)],[F(0),F(0),F(1,2),F(1,2)],[F(0),F(0),F(1,2),F(1,2)]]
 for x in range(4):
  assert sum(K[x])==1
  for y in range(4):assert pi[x]*K[x][y]==pi[y]*K[y][x]
 A={0,1,2};U={0};V={0,1};W={1};q=sum(pi[x] for x in A)
 r=max(sum(K[x][y] for y in range(4) if y not in A) for x in A)
 e1=max(sum(K[x][y] for y in range(4) if y not in V) for x in A&U)
 e2=max(sum(K[x][y] for y in range(4) if y not in W) for x in A&V)
 p=sum(pi[x] for x in A&(U-W))/q
 assert p<= (e1+e2)/(1-r)<1 and r>0
 restricted=[[K[x][y] if y in A and y!=x else F(0) for y in range(4)] for x in range(4)]
 for x in A:restricted[x][x]=1-sum(restricted[x])
 for y in A:assert sum(pi[x]*restricted[x][y] for x in A)==pi[y]
 # Cube = Q_3, spectrum 3,1,-1,-3 with multiplicities 1,3,3,1.
 # Disjoint identical copies multiply every multiplicity. Permutations preserve characteristic polynomial.
 multiplicities={str(m):[m,3*m,3*m,m] for m in (2,3,5,11)}
 for m,ms in multiplicities.items():assert all(x%int(m)==0 for x in ms)
 return dict(status='PASS_EXACT_BOOKKEEPING_ONLY',scale=scale,weighted_restriction={'p':str(p),'r':str(r),'epsilon1':str(e1),'epsilon2':str(e2),'bound':str((e1+e2)/(1-r))},multiplicities=multiplicities,limitation='Finite checks are not proof verdicts. Cube copies illustrate multiplicity only, not an asymptotic high-girth counterexample; the report gives the latter analytically.')
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
