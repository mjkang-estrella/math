from finite_checks import gamma
import json
from pathlib import Path
L=Path(__file__).resolve().parents[1];out=[]
for k in range(2,101):
 n,E=gamma(k);m,F=gamma(k-1);x=m-1;c=m;b=m+1;a=m+2
 N={v if u==x else u for u,v in F if x in (u,v)}
 G=F|{tuple(sorted(e)) for e in [(a,b),(b,c),(c,x)]+[(a,v) for v in N]}
 out.append({'k':k,'n':n,'trung_graph_equals_source_graph':E==G,'old_terminal_neighbors':sorted(v+1 for v in N)})
assert all(r['trung_graph_equals_source_graph'] for r in out)
(L/'outputs/trung-bridge-check.json').write_text(json.dumps(out,indent=2));print('Checked k=2..100; all exact edge set identities passed. General proof is in mathematical-attempts.md; script is diagnostic.')
