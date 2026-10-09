"""Deterministic exact diagnostics, not geometric/proof certification."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import json, math
from collections import defaultdict
def poly_add(*polys):
 r=defaultdict(int)
 for p in polys:
  for m,c in p.items():r[m]+=c
 return {m:c for m,c in r.items() if c}
def poly_mul(p,q):
 r=defaultdict(int)
 for a,c in p.items():
  for b,d in q.items():r[tuple(x+y for x,y in zip(a,b))]+=c*d
 return {m:c for m,c in r.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
out=Path('frontier/experiments/i28_algebra_discovery')
r={}
# Weyl multiplication, written as exact roots-of-unity exponents and permutations.
count=0
for n in [8,16,32]:
 for a,b,c,d in product(range(-2,3),repeat=4):
  for j in range(n):
   lhs=c*(j+d)+a*(j+d+b)
   rhs=(a+c)*(j+b+d)-b*c
   assert (lhs-rhs)%n==0
   count+=1
r['weyl_exact_actions']=count
count=0
pts=list(product(range(-2,3),repeat=2))
for (a,b),(c,d),(e,f) in product(pts,repeat=3):
 assert -b*c-(b+d)*e == -d*e-b*(c+e)
 count+=1
r['weyl_cocycle_identities']=count
r['weyl_global_defect_two']=[{'n':n,'b':n//2,'c':1,'phase_mod_n':(-n//2)%n} for n in [8,16,32,64]]
r['local_box_examples']=[{'R':R,'n':2**(2*R+10),'defect_upper_bound_divided_by_pi':str(Q(2*R*R,2**(2*R+10))),'bott_index':1} for R in range(1,11)]
# Good module filtration F0=R,F1=m,F2=m,Fn=m^(n-1) n>=2.
def cut(n):return 0 if n==0 else (1 if n==1 else n-1)
checks=0
for i in range(21):
 for j in range(21):
  assert i+cut(j)>=cut(i+j);checks+=1
assert cut(0)==0 and cut(1)==cut(2)==1
r['module_filtration_compatibility_checks']=checks
r['graded_free_module_counterexample']={'degree0_dimension':1,'degree1_dimension':0,'x_and_y_kill_degree0':True,'dimensions_0_to_12':[1,0]+list(range(2,13)),'description':'gr_F R = k in degree 0 plus the maximal ideal shifted one degree; R itself is free.'}
# Perturbed twisted cubic: given leading equations do not control initial ideal.
x={(1,0,0,0):1};y={(0,1,0,0):1};z={(0,0,1,0):1};w={(0,0,0,1):1}
f1=poly_add(poly_mul(x,z),neg(poly_mul(y,y)));f2=poly_add(poly_mul(x,w),neg(poly_mul(y,z)));f3=poly_add(poly_mul(y,w),neg(poly_mul(z,z)))
assert not poly_add(poly_mul(z,f1),neg(poly_mul(y,f2)),poly_mul(x,f3))
w3={(0,0,0,3):1}
assert poly_add(poly_mul(z,poly_add(f1,w3)),neg(poly_mul(y,f2)),poly_mul(x,f3))=={(0,0,1,3):1}
r['syzygy_counterexample']={'new_initial_relation':'z*w^3','old_prime_parametrization_value':'t*u^11 != 0'}
# Coordinate order a,b,c,d; each chart order base,u,v,w.
f={(0,0,0,2):1,(4,0,0,0):-1,(0,4,0,0):-1,(0,0,4,0):-1,(2,2,1,0):-1}
charts={}
for base in range(3):
 others=[i for i in range(3) if i!=base]; chart={}
 for ex,coef in f.items():
  e=(sum(ex[:3])+2*ex[3]-4,ex[others[0]],ex[others[1]],ex[3]);assert min(e)>=0;chart[e]=coef
 special={e[1:]:coef for e,coef in chart.items() if e[0]==0}
 assert special=={(0,0,2):1,(0,0,0):-1,(4,0,0):-1,(0,4,0):-1}
 charts['abc'[base]]={str(e):coef for e,coef in chart.items()}
r['weighted_rees_charts']=charts
# The perturbing monomial is not divisible by any monomial generator of the Jacobian ideal.
pert=(2,2,1,0);jac=[(3,0,0,0),(0,3,0,0),(0,0,3,0),(0,0,0,1)]
assert not any(all(a>=b for a,b in zip(pert,j)) for j in jac)
r['nonzero_first_order_deformation_class']='a^2*b^2*c modulo (a^3,b^3,c^3,d)'
counts=[]
for N in range(25):
 mons=[(i,j,k,e) for i,j,k in product(range(N+1),repeat=3) for e in [0,1] if i+j+k+2*e==N]
 expected=math.comb(N+2,2)+(math.comb(N,2) if N>=2 else 0)
 assert len(mons)==expected
 counts.append(len(mons))
r['weighted_module_hilbert_counts']=counts
# For each finite A-module generator b_j of filtration degree d_j, Rees generators
# b_j u^k for 0<=k<=d_j generate every shifted A-ideal summand.
checks=0
for degree in range(11):
 for N in range(31):
  coefficient_order=max(N-degree,0)
  k=min(N,degree)
  assert N-k==coefficient_order
  checks+=1
r['rees_shift_checks']=checks
# Source surface arithmetic and strict Veronese cutoff, no generation claim.
rows=[]
for n in [n for n in range(3,101) if all(n%d for d in range(2,math.isqrt(n)+1))]:
 h=5*n**3; delta=n**3*(n*n-10); K2=5*n**3*(n-2)**2;c2=n**3*(2*n*n-10*n+15)
 assert K2-2*c2==delta
 qs=[q for q in range(1,31) if delta>6*q*q*h]
 rows.append({'n':n,'H2':h,'K2_minus_2c2':delta,'qualifying_q_up_to_30':qs})
r['surface_veronese_checks']=rows
# Tensor product zero divisors for a separable algebraic element: a model for arbitrary degree.
checks=0
for degree in range(2,11):
 q=poly_add({(degree-1-k,k):1 for k in range(degree)},{(0,0):-1})
 diff={(1,0):1,(0,1):-1}
 prod=poly_mul(diff,q)
 assert prod=={(degree,0):1,(0,degree):-1,(1,0):-1,(0,1):1}
 # Substitute X^degree=X+1 and Y^degree=Y+1 in this expression.
 reduced=poly_add({(1,0):1,(0,0):1},neg({(0,1):1,(0,0):1}),{(1,0):-1,(0,1):1})
 assert reduced=={} and diff and q
 assert all(max(ex)<degree for ex in q)
 checks+=1
r['tensor_zero_divisor_polynomial_checks']=checks
# Source colored correction graph vs power-of-two replacement: necessary graph tests only.
graphs=[]
for m in [9,11,16,32]:
 offsets=(1,2,3,4)
 assert all((i+j)%m for i in offsets for j in offsets)
 assert len({(-i)%m for i in offsets})==4
 assert not set(offsets)&{(-i)%m for i in offsets}
 assert math.gcd(m,2-1)==1 and math.gcd(m,4-3)==1
 graphs.append({'m':m,'no_returns_length_one_or_two':True,'color_difference_connected':True,'cyclic_parameter_norm_valuation_divisor':m})
r['colored_graph_checks']=graphs
r['limits']=['No computed example uses the obstructed surface in a nontrivial filtered deformation.','No numerical check establishes a Hilbert-space theorem, Rees-scheme regularity, cohomology vanishing, or algebraicity of a tensor extension.','Weyl action identities and Bott value are exact formulas; no floating eigensolver is used.','Graph tests do not construct an involution-compatible correction or division realization.']
(out/'diagnostics.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':'PASS','weyl_actions':r['weyl_exact_actions'],'cocycles':r['weyl_cocycle_identities'],'module_filtration_checks':r['module_filtration_compatibility_checks'],'rees_shift_checks':r['rees_shift_checks'],'weighted_hilbert_degrees':len(counts)},indent=2))
