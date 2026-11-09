from pathlib import Path
import json
L=Path(__file__).resolve().parent
for p in L.glob('word-collision-?.json'):
 x=json.loads(p.read_text());print(p.name,x['pair'],x['first_difference'])
t=json.loads((L/'http/omega-root.json').read_text());jobs=[]
for x in t['tree']:
 if x['path']=='Problems':jobs.append(['omega-Problems-tree.json',x['url']+'?recursive=1'])
(L/'omega-problems-jobs.json').write_text(json.dumps(jobs));print('Problems jobs',len(jobs))
