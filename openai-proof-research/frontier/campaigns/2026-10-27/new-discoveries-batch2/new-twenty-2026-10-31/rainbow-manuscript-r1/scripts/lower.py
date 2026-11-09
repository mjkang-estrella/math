import json,itertools
from pathlib import Path
P=Path(__file__).resolve().parents[1]; a=json.loads((P/'evidence/original/outputs/rainbow-certificate.json').read_text())[1]['adjacency']
for x,y in itertools.combinations(range(8),2):
 if not a[x]>>y&1:continue
 paths=[]
 def dfs(v,p):
  if v==y:paths.append(p);return
  for w in range(8):
   if a[v]>>w&1 and w not in p and {v,w}!={x,y}:dfs(w,p+[w])
 dfs(x,[x])
 for p,q in itertools.combinations(paths,2):
  if not set(p[1:-1])&set(q[1:-1]):print(x,y,p,q);raise SystemExit
