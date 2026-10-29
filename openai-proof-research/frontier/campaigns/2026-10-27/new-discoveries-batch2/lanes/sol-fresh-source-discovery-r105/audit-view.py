import json,pathlib,re
L=pathlib.Path(__file__).parent;d=json.loads((L/'duplicate-expanded-summary.json').read_text())
for x in d['hit_files']:
 print(x['path'])
 for h in x['hits']:
  if not re.search(r'Heilbronn',h['context'],re.I):print(h['context'][:550])
