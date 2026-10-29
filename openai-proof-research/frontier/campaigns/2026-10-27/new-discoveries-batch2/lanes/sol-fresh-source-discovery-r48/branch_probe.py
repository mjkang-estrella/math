from check import treecalc,unimodal
import json
from pathlib import Path
# Four designed branching shapes; each delay list has one valley in leaf order.
cases=[([-1,0,1,1,0,4,4],{2:2,3:1,5:1,6:2}),([-1,0,1,1,0,4,4],{2:3,3:1,5:1,6:2}),([-1,0,1,2,2,0,5,5],{3:2,4:1,6:1,7:3}),([-1,0,1,1,0,4,5,5],{2:3,3:1,6:1,7:2}),([-1,0,1,1,0,4,4],{2:1,3:1,5:2,6:3}),([-1,0,1,1,0,4,4],{2:3,3:2,5:1,6:1})]
a=[]
for p,d in cases:
 q=treecalc(p,d);a.append({'parents':p,'delays':d,'Q':q,'unimodal':unimodal(q)})
Path('branch-checks.json').write_text(json.dumps(a,indent=2));print(json.dumps(a))
