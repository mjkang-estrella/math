from itertools import combinations
from pathlib import Path
import json
P=Path(__file__).resolve().parent
rows=[]
for isolates in range(4):
 n=4+isolates;edges=[(0,1),(0,2),(0,3)];vals=[]
 for a in combinations(range(n),n//2):
  s=set(a);vals.append(sum((u in s)!=(v in s) for u,v in edges))
 rows.append(dict(graph='K1,3 plus isolated vertices',isolates=isolates,n=n,bisections_enumerated=len(vals),maximum_cut_edges=max(vals),total_edges=3))
(P/'calculation.json').write_text(json.dumps(dict(executed=True,scope='Only four specified unweighted graphs; not a conjecture sweep',rows=rows,conclusion='Adding at least one isolate repairs the claw obstruction. Proposed disconnected-claw shortcut fails.'),indent=2)+'\n')
print((P/'calculation.json').read_text())
