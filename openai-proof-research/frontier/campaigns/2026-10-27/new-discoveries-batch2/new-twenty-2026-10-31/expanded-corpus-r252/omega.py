from pathlib import Path
import json
L=Path(__file__).resolve().parent;D=L/'http';j=[]
p=D/'omega-root.json'
if p.exists():
 t=json.loads(p.read_text())
 for x in t['tree']:
  if x['type']=='tree' and x['path'] in ['Blueprint','Lean','lean','papers','preprints','conjectures','Conjectures']:
   j.append(['omega-'+x['path']+'-sub.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{x["sha"]}?recursive=1'])
 print([(x['path'],x['type']) for x in t['tree']])
(L/'omega-plan.json').write_text(json.dumps(j))
