import ast,json,sys,itertools,random
from pathlib import Path
from functools import reduce
from operator import xor
N=32
for fn,closed in [('sources/author-open32-27.py.txt',True),('sources/author-open32-5.py.txt',False)]:
 tree=ast.parse(Path(fn).read_text());vals={}
 for stmt in tree.body:
  if isinstance(stmt,ast.Assign) and isinstance(stmt.targets[0],ast.Name) and stmt.targets[0].id in ['nbhd','labeling']:vals[stmt.targets[0].id]=ast.literal_eval(stmt.value)
 ne=vals['nbhd'];labels={u:int(''.join(map(str,a)),2) for u,a in vals['labeling'].items()};E={(min(labels[u],labels[v]),max(labels[u],labels[v])) for u in ne for v in ne[u]}
 if closed:E=set(itertools.combinations(range(N),2))-E
 d=len(E)*2//N
 Path(f'outputs/seed-{N}-{d}-{int(closed)}.json').write_text(json.dumps(dict(N=N,d=d,closed=closed,edges=sorted(E)),indent=2))
print('source graph extracted as literals, no execution')
