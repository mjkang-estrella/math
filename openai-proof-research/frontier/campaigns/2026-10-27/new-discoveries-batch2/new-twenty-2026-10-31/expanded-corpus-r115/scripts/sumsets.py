from itertools import combinations
from math import gcd
from functools import reduce
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];rows=[]
for d in range(3,26):
 for k in range(3,min(d+1,8)+1):
  # cap binomial spaces independently; exact coverage recorded
  import math
  if math.comb(d-1,k-2)>200000:continue
  B=tuple(range(k-1))+(d,);ref=[1]
  for h in range(1,17):ref.append(reduce(int.__or__,(ref[-1]<<a for a in B),0))
  cnt=0;bad=[]
  for inner in combinations(range(1,d),k-2):
   A=(0,)+inner+(d,)
   if reduce(gcd,A)!=1:continue
   cnt+=1;s=1
   for h in range(1,17):
    s=reduce(int.__or__,(s<<a for a in A),0)
    if s.bit_count()<ref[h].bit_count():bad.append(dict(A=A,h=h,lhs=s.bit_count(),rhs=ref[h].bit_count()))
  row=dict(d=d,k=k,h_range=[1,16],normalized_sets=cnt,counterexamples=bad[:5]);rows.append(row)
  print(json.dumps(row),flush=True)
  (D/'outputs/sumsets.json').write_text(json.dumps(rows,indent=2)+'\n')
  if bad:raise SystemExit
