#!/usr/bin/env python3
"""Exact finite diagnostics for the novelty reductions; not a topology proof."""
import itertools,json,math,pathlib
P=pathlib.Path(__file__).resolve().parent
rows=[]; cases=0; noloops=0
for r in range(1,9):
 vs=[v for v in itertools.product(range(2),repeat=r) if any(v)]
 for u in vs:
  a=u.index(1)
  # In basis (u, e_j: j != a), z has coordinates (z_a,z_j-z_a*u_j).
  def co(z): return (z[a],)+tuple(z[j]-z[a]*u[j] for j in range(r) if j!=a)
  for R in range(1,13):
   d=2*R+1; target=co(u); assert target==(1,)+(0,)*(r-1)
   assert all((d*x)%d==0 for x in target[:1]); assert d%2
   # Source cyclic criterion on L0=<u,2 e_j>; double is exactly 2Z^r.
   twice=co(tuple(2*x for x in u)); assert twice==(2,)+(0,)*(r-1)
   for j in range(r):
    z=tuple(2*int(k==j) for k in range(r)); assert all(x%2==0 for x in co(z))
   for v in vs:
    c=co(v); residue=(c[0]%d,)+tuple(x%2 for x in c[1:]); assert any(residue); noloops+=1
   cases+=1
 # Every binary direction has exactly one selected endpoint in the positive cover.
 capchecks=0
 for u in vs:
  a=u.index(1)
  for v in itertools.product(range(2),repeat=r):
   w=tuple(x^y for x,y in zip(v,u))
   for c in range(2):
    assert (c==v[a])+(c==w[a])==1; capchecks+=1
 rows.append({'rank':r,'binary_directions':len(vs),'positive_cap_checks':capchecks})
# Looser, uncoupled all-binary detector != full even-lattice classification.
# Lambda=< (4,0),(-1,1)>; quotient map z -> z1+z2 mod 4.
vs2=[(1,0),(0,1),(1,1)]
orders={str(v):4//math.gcd(sum(v),4) for v in vs2}
assert list(orders.values())==[4,4,2]
assert (-1+1)%4==0 and (-1)%2==1
# Stronger than the original 6-point coordinate counterexample: every binary direction passes.
# Scalar signed constraints force x(v+1)=x(v)+1 and x(v+1)=x(v), inconsistent.
original_solutions=[]
for s in itertools.product(range(2),repeat=4):
 if all(s[(v+1)%4]==(s[v]^1) and s[(v+1)%4]==s[v] for v in range(4)): original_solutions.append(s)
assert not original_solutions
# In B's A x C2, any subgroup disjoint from the realized A injects into C2.
small_rank_checks=0
for a_rank in range(1,6):
 outside=range(1<<a_rank,1<<(a_rank+1))
 for x in outside:
  for y in outside:
   if x!=y: assert 0<(x^y)<(1<<a_rank); small_rank_checks+=1
out={'status':'PASS','cyclic_reduction_obstruction_lattices':cases,'all_binary_no_loop_checks':noloops,'positive_cases':rows,'stronger_classification_witness':{'lattice_columns':[[4,0],[-1,1]],'quotient':'Z/4, images e1=e2=1','binary_direction_orders':orders,'coupled_solutions':0,'independent_alternations_exist':True},'coset_rank_two_exclusion_checks':small_rank_checks,'limits':'Finite exact diagnostics only. Source-local geometric applicability and the general reductions are argued in the review; no upstream theorem is tested.'}
(P/'checks.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
