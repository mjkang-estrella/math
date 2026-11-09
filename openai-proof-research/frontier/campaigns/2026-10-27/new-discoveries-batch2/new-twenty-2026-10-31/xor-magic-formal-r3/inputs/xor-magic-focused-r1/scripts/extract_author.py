import ast,json
from pathlib import Path
for p in Path('sources').glob('author-open*.py.txt'):
 vals={}
 for stmt in ast.parse(p.read_text()).body:
  if isinstance(stmt,ast.Assign) and isinstance(stmt.targets[0],ast.Name) and stmt.targets[0].id in ['nbhd','labeling']:vals[stmt.targets[0].id]=ast.literal_eval(stmt.value)
 labels={u:int(''.join(map(str,a)),2) for u,a in vals['labeling'].items()};assert set(labels.values())==set(range(len(labels)));E=sorted({tuple(sorted((labels[u],labels[v]))) for u,a in vals['nbhd'].items() for v in a});N=len(labels);g=dict(N=N,d=2*len(E)//N,closed=False,edges=E)
 Path('outputs/'+p.stem+'.json').write_text(json.dumps(g))
