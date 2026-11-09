from pathlib import Path
from itertools import combinations,combinations_with_replacement
import json
D=Path(__file__).resolve().parents[1];out=[]
for n in [5,6,7,8]:
 for k in range(2,min(n,4)+1):
  cap=14 if n<=6 else 10
  losing={};moves=list(combinations(range(n),k));count=0;trans=0
  for x in combinations_with_replacement(range(cap+1),n):
   win=False
   for s in moves:
    if x[s[0]]==0:continue
    y=list(x)
    for i in s:y[i]-=1
    y=tuple(sorted(y));trans+=1
    if losing[y]:win=True;break
   losing[x]=not win;count+=not win
  # lex ordering of sorted vectors is topological for unit removals.
  shift_matches=shift_tests=0
  for x,p in losing.items():
   if x[-1]+2<=cap:
    shift_tests+=1;shift_matches+=(p==losing[tuple(t+2 for t in x)])
  r={'n':n,'k':k,'coordinate_cap':cap,'sorted_positions':len(losing),'P_positions':count,'transitions_considered':trans,'uniform_shift2_tests':shift_tests,'uniform_shift2_matches':shift_matches,'meaning':'finite diagnostic only; no semilinearity inference'};out.append(r);print(r,flush=True)
(D/'outputs/nim.json').write_text(json.dumps(out,indent=2))
