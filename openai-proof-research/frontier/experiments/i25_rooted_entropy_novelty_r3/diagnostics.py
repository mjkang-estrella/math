"""Exact, small tests of significance comparisons, not a full proof audit."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import json
root=Path(__file__).resolve().parents[3];out=root/'frontier/experiments/i25_rooted_entropy_novelty_r3/diagnostics.json'
# Every edge's charge under root propagation, independently of its marginal.
checks=0
for n in (6,8,10):
 E=list(combinations(range(n),2))
 for k in range(3,n-2,2):
  S=set(range(k));C=[e for e in E if (e[0] in S)!=(e[1] in S)]
  for v in range(n):
   A=S if v in S else set(range(n))-S;Z=n
   for e in E:
    inA=[u in A for u in e]
    child1=e if all(inA) else tuple(u if u in A else Z for u in e) if any(inA) else None
    child2=e if not any(inA) else tuple(Z if u in A else u for u in e) if not all(inA) else None
    parent=int(v not in e)
    charged1=int(child1 is not None and v not in child1)
    charged2=int(child2 is not None and Z not in child2)
    assert parent==charged1+charged2;checks+=1
trace=[]
for m in range(3,101):
 for eps in (Q(1,1000),Q(1,10),Q(1)):
  c=Q(3,2)+eps
  no_cut=-2*m+m+c*(m-1)
  all_faces=-3*m+2+m+c*(m-1)
  assert no_cut==Q(m-3,2)+eps*(m-1)>0
  assert all_faces==(c-2)*(m-1)
  trace.append(dict(m=m,epsilon=str(eps),no_cut=str(no_cut),general_rank=str(all_faces)))
# K6 minus a fixed PM: source H >= F/m still misses the rooted target.
assert 3**9>4**7  # 2 log 4 > 9 log(4/3)
# A five-atom law on a 1-factorization of K6 violates the arbitrary-law variant.
verts=set(range(6));factors=[]
for i in range(5):
 M=[tuple(sorted((5,i)))]+[tuple(sorted(((i+j)%5,(i-j)%5))) for j in (1,2)]
 assert set(sum((list(e) for e in M),[]))==verts;factors.append(M)
assert len(set(e for M in factors for e in M))==15
assert 4**12>5**10 # 2 log 5 > 12 log(5/4)
r=dict(status='PASS',scope='Exact algebra and scope checks only; no universal entropy proof or numerical optimization certificate.',charged_edge_checks=checks,trace_checks=len(trace),trace=trace,degree_four_scalar_certificate=dict(left=3**9,right=4**7,interpretation='2 log 4 - 9 log(4/3) > 0'),arbitrary_law_counterexample=dict(graph='K6',matching_law='uniform over these five disjoint perfect matchings',factors=factors,comparison='F-Ent=2 log5 > (3/2)(B-b_v)=12 log(5/4)',left=4**12,right=5**10),unrooted_general_trace='2+(c-2)m',rooted_general_trace='(c-2)(m-1)',rooted_no_cut_trace='(c-1)m-c')
out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ['trace','arbitrary_law_counterexample']},indent=2))
