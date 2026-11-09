from pathlib import Path
import json
L=Path(__file__).resolve().parent;t=json.loads((L/'http/omega-tree.json').read_text());jobs=[]
for x in t['tree']:
 if x['path'] in ('D5','Problems'):
  print(x['path'],x['sha']);jobs.append(['omega-'+x['path']+'-tree.json',x['url']+'?recursive=1'])
(L/'omega-sub-jobs.json').write_text(json.dumps(jobs))
