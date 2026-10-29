from structured import calc
from formulas import G,add,mul
from itertools import permutations
from pathlib import Path
import json
old=[-1,0,1,0,3];N=4
# Old incomparable preorder pairs; parent1 has rank t on the left, parent3 on right.
pairs=[(1,3),(1,4),(2,3),(2,4)]
rows=[]
for a in (1,2):
 for side in ('left','right'):
  full=([-1,0,1,1,0,4] if a==1 else [-1,0,1,2,1,0,5]) if side=='left' else ([-1,0,1,0,3,3] if a==1 else [-1,0,1,0,3,3,5])
  leaf=(2 if a==1 else 3) if side=='left' else (5 if a==1 else 6);parent=1 if side=='left' else 3
  ranked={}
  for perm in permutations(range(1,5)):
   pos={v:i+1 for i,v in enumerate(perm)}
   if pos[2]>pos[1] or pos[4]>pos[3]:continue
   e=sum(pos[u]<pos[v] for u,v in pairs);t=pos[parent];ranked[t]=add(ranked.get(t,(0,)),(1,),e)
  for d in range(1,6):
   q,_=calc(full,{v:(d if v==leaf else 1) for v in range(1,len(full)) if v not in full});rhs=(0,)
   for t,poly in ranked.items():
    if t<d:continue
    shift=a*(N-t) if side=='left' else a*(d-1)
    rhs=add(rhs,mul(poly,G(t-d+a,a)),shift)
   while len(rhs)>1 and rhs[-1]==0:rhs=rhs[:-1]
   assert q==rhs,(a,side,d,q,rhs)
   rows.append(dict(twig_length=a,side=side,release=d,Q=q,ranked_old=ranked))
Path('rank-checks.json').write_text(json.dumps(rows,indent=2));print('extremal twig rank transform: 20 PASS')
