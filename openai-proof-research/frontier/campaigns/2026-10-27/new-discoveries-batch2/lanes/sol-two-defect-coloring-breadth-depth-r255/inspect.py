import json,pathlib,collections
L=pathlib.Path(__file__).parent
for s in ['F','C']:
 t=json.loads((L/(s+'-table.json')).read_text());print(s,collections.Counter(r['cost'] for r in t['rows']))
