from pathlib import Path
from functools import lru_cache
from itertools import combinations
import json
D=Path(__file__).resolve().parents[1]
def val(n,edges,q):
 @lru_cache(None)
 def f(t,turn,left):
  loads=[sum(t[i] for i in e) for e in edges]
  if all(x>=q for x in loads):return 0
  choices=[]
  for i in range(n):
   if any(i in e and load<q for e,load in zip(edges,loads)):
    u=list(t);u[i]+=1
    choices.append(1+f(tuple(u),1-turn,q) if left==1 else 1+f(tuple(u),turn,left-1))
  return (min if turn==0 else max)(choices)
 return f((0,)*n,0,q),f.cache_info().currsize
out=[]
for n in [2,3,4]:
 universe=[tuple(i for i in range(n) if s>>i&1) for s in range(1,1<<n)]
 families=[]
 for mask in range(1,1<<len(universe)):
  es=[e for j,e in enumerate(universe) if mask>>j&1]
  if n==4 and any(set(e)<set(g) for e in es for g in es):continue
  families.append(es)
 counts={};fails=[];states=0
 for q in [1,2,3,4]:
  gaps={}
  for num,es in enumerate(families):
   a,ss=val(n,es,q);states+=ss;b,_=val(n,es,1);gap=a-q*b;gaps[gap]=gaps.get(gap,0)+1
   if gap>0:fails.append({'q':q,'edges':es,'ticks':a,'integer':b})
  counts[q]=gaps
  print(n,q,len(families),'gaps',gaps,flush=True)
 out.append({'n':n,'family':'all nonempty hypergraphs' if n<4 else 'nonempty inclusion antichains (not all hypergraphs)','count':len(families),'gaps_in_ticks':counts,'positive_grid_gaps':fails,'states_total':states})
(D/'outputs/fractional.json').write_text(json.dumps(out,indent=2))
