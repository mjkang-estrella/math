from pathlib import Path
import json
L=Path(__file__).resolve().parent;D=L/'http';j=[]
t=json.loads((D/'openai-root.json').read_text())
for x in t['tree']:
 if x['path'] in ['preprints','lean']:j.append(['openai-'+x['path']+'-complete.json',f'https://api.github.com/repos/openai/math/git/trees/{x["sha"]}?recursive=1'])
t=json.loads((D/'pool-tree.json').read_text());print('POOL',t.get('truncated'),len(t['tree']))
for x in t['tree']:
 p=x['path']
 if p.endswith('projects.yml'):j.append(['pool-projects.yml',f'https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/{p}'])
print('jobs',j)
(L/'subtrees-plan.json').write_text(json.dumps(j))
for name in ['omega','pool']:
 d=json.loads((L/'registry-screen.json').read_text())[name]; print(name,d['truncated']);print('\n'.join(p for p in d['hits'] if not '/Algebra' in p)[:9000])
