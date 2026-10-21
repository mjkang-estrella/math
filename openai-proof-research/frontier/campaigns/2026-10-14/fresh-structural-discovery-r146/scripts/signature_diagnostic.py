"""Exact finite diagnostic only, not a counter implementation or mathematical gate."""
from fractions import Fraction as F
from pathlib import Path
import json,itertools
ROOT=Path(__file__).resolve().parents[1]
Q=[[F(1,16),F(1),F(1,2)],[F(1),F(1,16),F(1,2)],[F(1,2),F(1,2),F(1)]]
def form(v,w):return sum(v[i]*Q[i][j]*w[j] for i in range(3) for j in range(3))
u=[1,1,0];v=[0,0,1];a=[1,-1,0]
R=[[form(u,u),form(u,v)],[form(v,u),form(v,v)]]
det=R[0][0]*R[1][1]-R[0][1]**2
assert R[0][0]>0 and det>0 and form(a,a)<0 and form(a,u)==form(a,v)==0
eps=F(1,10);robust=F(17,8)*(1-eps)**2-(1+eps)**2
assert robust>0
thresholds=[]
for t in [F(1),F(1,2),F(12,25)]:
 determinant=t*t*(t*t/F(8)+2*t-1)
 thresholds.append({'t':str(t),'symmetric_det':str(determinant),'at_most_one_positive':determinant<=0})
assert thresholds[0]['at_most_one_positive']==False
assert thresholds[1]['at_most_one_positive']==False
assert thresholds[2]['at_most_one_positive']==True
# Exact weighted shift tests on two partition-polymatroid supports in dimension3.
# Each a_i(k) = 2^{-(k-mode_i)^2}; paired factors have arbitrary distinct modes.
def ranks(part, caps):
 return [sum(c for block,c in zip(part,caps) if any(mask>>e&1 for e in block)) for mask in range(8)]
def bases(r):
 R=r[-1]
 return [x for x in itertools.product(range(R+1),repeat=3) if sum(x)==R and all(sum(x[e] for e in range(3) if mask>>e&1)<=r[mask] for mask in range(8))]
cases=checks=0
for Rtot in range(1,5):
 rr1=ranks([(0,1,2)],[Rtot])
 for a0 in range(Rtot+1):
  rr2=ranks([(0,1),(2,)],[a0,Rtot-a0])
  X=bases(rr1);Y=bases(rr2)
  for mode1,mode2 in [((0,0,0),(0,0,0)),((1,0,2),(0,2,1))]:
   counts={}
   for x in X:
    for y in Y:
     d=tuple(x[i]-y[i] for i in range(3)); q=F(1,2**sum((x[i]-mode1[i])**2+(y[i]-mode2[i])**2 for i in range(3)))
     counts[d]=counts.get(d,F(0))+q
   for j,k in itertools.combinations(range(3),2):
    for d,mass in counts.items():
     dm=list(d);dp=list(d);dm[j]-=1;dm[k]+=1;dp[j]+=1;dp[k]-=1
     assert mass**2>=counts.get(tuple(dm),0)*counts.get(tuple(dp),0)
     checks+=1
   cases+=1
original={frozenset(x) for x in [(1,3),(1,4),(2,3),(2,4)]}
slab={x for x in original if len(x&{1,3})<=1}
B=frozenset({1,4});C=frozenset({2,3});removed=4
assert B in slab and C in slab
assert all((B-{removed})|{added} not in slab for added in C-B)
out={'matrix':[[str(x) for x in row] for row in Q], 'symmetric_restriction':[[str(x) for x in row] for row in R], 'positive_restriction_det':str(det),'negative_axis_value':str(form(a,a)),'ten_percent_robust_margin':str(robust),'regularizer_checks':thresholds,'slice_nonexchange':{'bases':[sorted(x) for x in sorted(slab,key=lambda x:sorted(x))],'from':[1,4],'toward':[2,3],'remove':4},'weighted_shift_cases':cases,'adjacent_checks':checks,'scope':'Exact diagnostic and small source-compatible weighted shift checks only; not full theorem, algorithm, or review.'}
(ROOT/'private/signature-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
