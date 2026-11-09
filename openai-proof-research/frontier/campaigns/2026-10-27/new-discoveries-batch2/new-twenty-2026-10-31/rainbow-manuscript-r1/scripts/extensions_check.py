from pathlib import Path
import json,itertools
P=Path(__file__).resolve().parents[1];out=[]
def reachable(a,x,y,s):
 seen={x}; todo=[x]
 while todo:
  v=todo.pop()
  for w in range(len(a)):
   if a[v]>>w&1 and not s>>w&1 and {v,w}!={x,y} and w not in seen:seen.add(w);todo.append(w)
 return y in seen
for f in json.loads((P/'evidence/review/extensions9.json').read_text())['failures']:
 a=f['adj'];b=[511^v^(1<<i) for i,v in enumerate(a)]
 for g,key in [(a,'rvd'),(b,'complement_rvd')]:
  c=f[key][1];certs=[]
  for x,y in itertools.combinations(range(9),2):
   for s in range(512):
    if s&(1<<x|1<<y):continue
    cols=[c[v] for v in range(9) if s>>v&1]
    if len(cols)!=len(set(cols)):continue
    if g[x]>>y&1 and c[x] in cols and c[y] in cols:continue
    if not reachable(g,x,y,s):certs.append([x,y,s]);break
   else:raise AssertionError((f['index'],key,x,y))
  out.append({'new_neighborhood':f['index'],'graph':key,'coloring':c,'cuts':certs})
(P/'extension-check.json').write_text(json.dumps(out,indent=2)+'\n');print('six extension colorings, 216 unordered pair cuts: PASS')
