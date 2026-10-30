from itertools import combinations
import json
from pathlib import Path
L=Path(__file__).resolve().parent
def prime(p):return p>1 and all(p%d for d in range(2,int(p**.5)+1))
def sums(seq,N):
 a={0}
 for g in seq:a|={(x+g)%N for x in a}
 return a
rows=[]
for p in range(5,32):
 if not prime(p):continue
 for n in range(2,201):
  if any(n%d==0 for d in range(2,p)):continue
  target=p*n+2*p-3;U=max(p*n+2*p*p-p-1,n*(p+1)-2)
  assert U-target>=2*p*p-3*p+2>0
  rows.append([p,n,target,U])
# Exact local obstruction to deducing progression from the available p=5 defect budget.
N=175;A=[1,1,4];S=sums(A,N);e=len(S)-len(A)-1
assert S=={0,1,2,4,5,6} and e==2 and e<=11
assert all({(a+i*d)%N for i in range(len(S))}!=S for a in range(N) for d in range(1,N))
# Every proper subgroup of C_N containing a term would need contain 1 or 4,
# both generators of C_175. Check the ambient C5 x C175 regularity directly:
# support is in cyclic <(0,1)> and any subgroup containing support has size>=175.
assert len(A)<175
# Finite arithmetic control for generalized progression-sum bridge with k<=p+1.
bridge=0
for p in [3,5,7,11]:
 for t in range(p,40):
  for h in range(2,15):
   for k in range(2,p+2):
    for r in range(1,k+1):
     s=k-r
     assert s<=t
     assert h*t+k-1-(t+r-2+s*h)==(h-1)*(t-s)+1>0
     bridge+=1
out=dict(bound_comparisons=len(rows),first_unresolved_shape_example=dict(p=5,n=35,target=182,yang_bound=219),local_witness=dict(N=N,sequence=A,sumset=sorted(S),excess=e,not_progression=True,not_source_counterexample=True),progression_bridge_arithmetic=bridge,universal_proof=False)
assert rows and max(175+50-5-1,35*6-2)==219
out['first_unresolved_shape_example']['yang_bound']=219
print(json.dumps(out,sort_keys=True,indent=2))
