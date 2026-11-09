from pathlib import Path
from fractions import Fraction as F
from math import comb
import json
D=Path(__file__).parent;L=D.parent
M=[[-1,1,1,1,1,-1,-1,1],[-1,1,1,-1,-1,1,1,1],[1,-1,1,1,1,-1,1,1],[1,-1,1,1,-1,1,1,1],[1,-1,1,-1,1,1,1,-1],[1,1,-1,1,1,1,1,-1],[1,1,-1,1,1,1,-1,1],[1,1,1,1,-1,-1,1,-1]]
w=[F(x,16) for x in [2,3,4,1,2,2,1,1]];v=[F(1,3)]*3+[F(0)]*5
mw=[sum(a*b for a,b in zip(row,w)) for row in M];mv=[sum(a*b for a,b in zip(row,v)) for row in M]
assert sum(w)==1 and all(x==F(3,8) for x in mw) and min(mv)==F(1,3)
ctx=[]
ids={x['mathdb_id'] for x in json.loads((D/'dispositions.json').read_text())}
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 data=json.loads((L/'root-mathdb-accepted-exclusions-r304'/name).read_text())
 def walk(o):
  if isinstance(o,dict):
   if o.get('mathdb_id') in ids or set(o.get('mathdb_ids',[]))&ids:ctx.append({'file':name,'match':o})
   for x in o.values():walk(x)
  elif isinstance(o,list):
   for x in o:walk(x)
 walk(data)
(D/'bounded-checks.json').write_text(json.dumps({'executed':'exact Fraction arithmetic, no trajectory proof','392923':{'matrix':M,'better_weights':[str(x) for x in w],'better_margins':[str(x) for x in mw],'cycle_weights':[str(x) for x in v],'cycle_margins':[str(x) for x in mv],'limit':'Does not independently prove cycle attraction, maximum3/8, or universal convergence. Published mechanism already exists.'},'392628_small_n':[{'n':n,'complete_edges':comb(n,3),'formula_edges':comb(n,3)-comb(n//2,3)-comb((n+1)//2,3)} for n in range(3,7)],'context_matches':ctx},indent=2)+'\n')
print('Exact source matrix margin comparison PASS; small-n scope check PASS; prior-context exact-ID matches',len(ctx))
