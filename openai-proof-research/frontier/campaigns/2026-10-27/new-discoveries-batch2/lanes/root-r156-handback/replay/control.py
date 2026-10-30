from checks import cover,verify
from itertools import combinations
from pathlib import Path
import json
L=Path(__file__).resolve().parent
def literal(n,t,starts):
 heads=set(starts);tails={a+t for a in starts};seen={1};path=[1]
 def rec(a):
  if len(path)==n:return a-t==1
  dest=[a-t] if a in tails else [a+d for d in (1,3,7) if a+d not in heads]
  for b in dest:
   if 1<=b<=n and b not in seen:
    seen.add(b);path.append(b)
    if rec(b):return True
    path.pop();seen.remove(b)
  return False
 return rec(1)
count=0
for t in (4,6,8):
 for n in range(t+2,min(2*t+1,12)+1):
  s=n-t
  for r in range(2,min(4,s)+1):
   for middle in combinations(range(2,s),r-2):
    starts=(1,)+middle+(s,);c,z=cover(n,t,starts)
    assert (c is not None)==literal(n,t,starts),(n,t,starts)
    if c:assert verify(c,n,t)
    count+=1
# Full three-backward-head possibilities at (n,t)=(21,16).
for a in (2,3,4):assert cover(21,16,(1,a,5))[0] is None
assert cover(21,16,(1,2,3,4,5))[0] is not None
out=dict(literal_dfs_controls=count,minimal_five_backward_example=dict(n=21,t=16),status='PASS',scope='Finite independent DFS controls only.')
(L/'control.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
