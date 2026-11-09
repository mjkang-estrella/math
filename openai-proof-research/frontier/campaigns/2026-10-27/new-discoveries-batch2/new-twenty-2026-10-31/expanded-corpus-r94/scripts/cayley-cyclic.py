from itertools import combinations
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];out=[]
for q in [3,5,7]:
 v=q*q-1;tested=0;found=[]
 # q=7 restricted arithmetic progression sets; full q5 exhaustive.
 sets=combinations(range(1,v),q) if q<7 else (tuple(sorted({(a+j*b)%v for j in range(q)}))for a in range(1,v)for b in range(1,v))
 for S in sets:
  if len(S)!=q or 0 in S or any(v-s in S for s in S):continue
  tested+=1;c=[0]*v
  for a in S:
   for b in S:
    if a!=b:c[(a-b)%v]+=1
  # zero common-neighbour equivalence class must be a subgroup of order q-1.
  H={0}|{i for i in range(1,v)if c[i]==0}
  if len(H)==q-1 and all(c[i]==1 for i in range(1,v)if i not in H)and all((a+b)%v in H for a in H for b in H):found.append(S)
 r=dict(q=q,group='cyclic',asymmetric_connection_sets_tested=tested,space='all subsets'if q<7 else 'arithmetic progressions only',solutions=found);print(r,flush=True);out.append(r)
(D/'outputs/cayley-cyclic.json').write_text(json.dumps(out,indent=2)+'\n')
