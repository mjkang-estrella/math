import json,sys
from pathlib import Path
from games import solve
L=Path(__file__).resolve().parent
out=[]
for sizes in [(5,5),(3,5),(5,5,5),(6,6),(3,3,3)]:
 edges=[];offset=0
 for n in sizes:
  edges += [(offset+i,offset+i+1) for i in range(n-1)];offset+=n
 out.append(dict(paths=sizes,total=solve(offset,edges,True),sum_component_D=sum(solve(n,[(i,i+1) for i in range(n-1)],True)[0] for n in sizes)))
(L/'component-check-results.json').write_text(json.dumps(out,indent=2));print(out)
