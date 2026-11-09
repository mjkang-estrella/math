from fractions import Fraction as Q
from pathlib import Path
import json,datetime
R=Path(__file__).resolve().parents[1]
# Replay a tiny published witness AFTER the source/successor checks; not a new result.
k=3;lam=mu=Q(1,3)
x=[Q(0),Q(2,9),Q(-1,3),Q(5,9),Q(2,3),Q(0)]
edges={'pm':(0,3,Q(1,3)),'pz':(0,5,Q(0)),'qm':(1,3,Q(2,3)),'qz':(1,5,Q(0)),'qw':(1,4,Q(2,3)),'tm':(2,3,Q(0))}
rows={
'qz':[(lam,[0,Q(2,3),0,Q(1,3),0,0]),(mu,[0,Q(1,3),0,Q(1,3),1,0]),(lam,[0,Q(-1,3),-1,1,1,0])],
'qm':[(lam+mu,[0,0,0,Q(1,3),1,0]),(lam,[0,Q(2,3),-1,1,0,0])],
'pz':[(lam,[1,Q(2,3),0,0,0,0]),(mu,[Q(-1,3),0,0,Q(2,3),1,0]),(lam,[Q(-2,3),0,-1,1,1,0])],
'pm':[(lam,[0,Q(2,3),0,0,0,0]),(mu,[0,0,0,Q(2,3),1,0]),(lam,[0,0,-1,1,1,0])]}
checks=0
for omitted,mix in rows.items():
 assert sum(w for w,p in mix)==1
 assert [sum(w*p[j] for w,p in mix) for j in range(6)]==x
 for w,p in mix:
  assert all(Q(p[j]).denominator==1 for j in [2,4,5])
  for e,(i,j,b) in edges.items():
   if e!=omitted:assert p[i]+p[j]>=b;checks+=1
F=3*(x[0]+x[1]+x[3]+x[5])+x[2]+x[4];assert F==Q(8,3)<3
# Literal strict-endpoint defect, with the symbolic c>0 observation in disposition.
assert 4==2**2 and 4-3+1==2 and 3>2
(R/'bounded-checks.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','purpose':'uncredited replay of already public k=3 certificate, plus literal endpoint defect','conforti':{'k':3,'point':list(map(str,x)),'cycle_edge_deletions':4,'rational_mixtures':11,'edge_inequalities':checks,'F':str(F),'separating_bound':3,'limits':'Does not replay universal separating-inequality proof, all-k algebra, normalised case, full literature or all proof dependencies. Read Sections 2–4 separately. Not a new counterexample.'},'binomial':{'n':4,'k':3,'binomial':4,'largest_prime_factor':2,'rhs_for_all_c_positive':2,'credit':0},'hard_sweeps':0,'resource_cap':'helper_guard fixed 512MiB AS/groupRSS CPU210s wall230s; no raises'},indent=2)+'\n')
print('PASS known certificate replay',checks,'edge checks')
