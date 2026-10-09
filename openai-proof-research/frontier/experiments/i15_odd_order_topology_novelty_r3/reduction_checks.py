"""Exact finite diagnostics for the uniform-arity reduction; not a geometric proof."""
from pathlib import Path
from itertools import product
import json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i15_odd_order_topology_novelty_r3'
def mul(a,b):return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2)) for i in range(2) for j in range(2))
def bracket(a,b):return tuple(x-y for x,y in zip(mul(a,b),mul(b,a)))
def comb(xs):return xs[0] if len(xs)==1 else bracket(xs[0],comb(xs[1:]))
def depth(q):return [1,1] if q==2 else [1]+[d+1 for d in depth(q-1)]
h=(1,0,0,-1);e=(0,1,0,0);f=(0,0,1,0)
rows=[]
for q in range(2,9):
 masks=[{i for i in range(q) if m>>i&1} for m in range(1,1<<q)]
 allowed=[(sorted(a),sorted(b)) for a in masks for b in masks if all(y==(x+1)%q for x in a for y in b)]
 assert len(allowed)==q and all(len(a)==len(b)==1 for a,b in allowed)
 assert { (a[0],b[0]) for a,b in allowed}=={(i,(i+1)%q) for i in range(q)}
 forbidden=[(a,b,k) for a,b in product(range(q),repeat=2) if b!=(a+1)%q for k in range(5)]
 assert len(forbidden)==5*q*(q-1)
 incidence=[sum(a==i for a,b,k in forbidden)+sum(b==i for a,b,k in forbidden) for i in range(q)]
 assert incidence==[10*(q-1)]*q
 # No forbidden pair with both deficient: at most one of five edges can be assigned
 # to each endpoint while that color remains deficient; 5 > 1 + 1.
 alloc=[sum(bits) for bits in product([0,1],repeat=5) if sum(bits)<=1 and 5-sum(bits)<=1]
 assert not alloc
 cycles=[]
 for d in range(1,3*q+1):
  count=sum((start+d)%q==start for start in range(q))
  assert (count>0)==(d%q==0)
  if d%q==0:
   # The abstract directed cycle retains distinct edge lifts even when d=2.
   chosen=[v%q for v in range(d)];none=one=two=0
   for v in range(d):
    for a,b,k in forbidden:
     n=int(a==chosen[v])+int(b==chosen[(v+1)%d]);none+=n==0;one+=n==1;two+=n==2
   assert two==0;assert one==10*(q-1)*d;assert none==5*(q-1)*(q-2)*d
  cycles.append({'degree':d,'successor_colorings':count})
 witness=bracket(comb([h]*(q-1)+[e]),comb([h]*(q-1)+[f]));expected=tuple((-4)**(q-1)*x for x in h)
 assert witness==expected and any(witness)
 depths=depth(q);assert len(depths)==q and depths[0]==1
 rows.append({'q':q,'deficiency_pairs_checked':len(masks)**2,'compatible_deficiency_pairs':allowed,'parallel_edges_per_step':len(forbidden),'ports_per_color':incidence[0],'right_comb_leaf_depths':depths,'caps_per_branch_choice':[2**d for d in depths],'sl2_witness':witness,'cycles':cycles})
assert rows[1]['caps_per_branch_choice']==[2,4,4]
# Majority obstruction for the one-hot encoded three-state successor relation.
states=[(1,0,0),(0,1,0),(0,0,1)];relation=[states[i]+states[(i+1)%3] for i in range(3)]
majority=tuple(int(sum(t[i] for t in relation)>=2) for i in range(6));assert majority not in relation and majority[:3]==majority[3:]
# Positive q=3 counts agree with I15; many edges have neither endpoint selected.
assert rows[1]['parallel_edges_per_step']==30 and rows[1]['ports_per_color']==20
result={'status':'PASS','scope':'Finite diagnostics for q=2,...,8; no claim that tests prove geometry, arbitrary q, source theorems, or topological realization. The written induction and source contracts are essential.','uniform_arity':rows,'majority_of_successor_pairs':majority,'i15_law_body_count':(20*19)**3*10**6*2**6}
assert result['i15_law_body_count']==3511808000000000
(S/'reduction-checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'PASS','q_checked':[2,8],'deficiency_pairs':sum(x['deficiency_pairs_checked'] for x in rows),'q3_caps':rows[1]['caps_per_branch_choice'],'q3_body_count':result['i15_law_body_count']},indent=2))
