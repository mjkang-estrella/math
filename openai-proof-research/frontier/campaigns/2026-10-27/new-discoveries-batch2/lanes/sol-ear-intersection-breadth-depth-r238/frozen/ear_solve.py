import json,signal,time,runpy
from pathlib import Path
L=Path(__file__).resolve().parent
ns=runpy.run_path(str(L/'checks.py'));weights=ns['weights'];cat=ns['cat']
results=[];start=time.monotonic();signal.alarm(45)
for n in range(5,11):
 w=weights(n);vs=list(w);adj={v:{u for u in vs if u!=v and u&v} for v in vs}
 best=[cat(n-3),[s for s in vs if s&1]];nodes=[0]
 def solve(candidates,score,chosen):
  nodes[0]+=1
  if not candidates:
   if score>best[0]:best[:]=score,chosen
   return
  # Partition the intersection graph into independent color classes.
  # Every clique uses <=1 vertex from each; sum of largest weights is an exact bound.
  colors=[]
  for v in sorted(candidates,key=lambda v:-w[v]):
   for c in colors:
    if all(not v&u for u in c):c.append(v);break
   else:colors.append([v])
  bound=sum(max(w[v] for v in c) for c in colors)
  if score+bound<=best[0]:return
  v=max(candidates,key=lambda v:(w[v],len(adj[v]&candidates)))
  solve(candidates&adj[v],score+w[v],chosen+[v])
  solve(candidates-{v},score,chosen)
 solve(set(vs),0,[])
 assert best[0]==cat(n-3)
 row={'n':n,'exact_maximum':best[0],'nodes':nodes[0],'seconds':time.monotonic()-start};results.append(row)
 (L/'ear-solve.json').write_text(json.dumps(results,indent=2));print(row,flush=True)
 # Test the elementary Talbot shift on literal weights, rather than assuming weight preservation.
 shifts=[]
 for s,a in w.items():
  if s>>(n-1)&1 and not s>>(n-3)&1:
   t=(s^(1<<(n-1)))|(1<<(n-2))
   if t in w and w[t]<a:shifts.append({'from':s,'to':t,'before':a,'after':w[t]})
 row['weight_losing_Talbot_shifts']=shifts[:3]
 (L/'ear-solve.json').write_text(json.dumps(results,indent=2))
