from pathlib import Path
import json
O=Path(__file__).parent;L=O.parent;B=L.parent
rows=json.loads((O/'assigned-records.json').read_text())
for x in rows:
 r=x['record'];print('\n###',r['mathdb_id'],r['title'],'\nSOURCE',r['source_url'],'\n'+r['statement'])
print('\nCAYLEY DECISION\n',next(L.glob('*r363/DECISION.md')).read_text())
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 data=json.loads((L/'root-mathdb-accepted-exclusions-r304'/name).read_text());print('HISTORY schema',name,type(data).__name__)
 # Exact assigned ID mentions only; no unassigned display.
 hits=[]
 def visit(x):
  if isinstance(x,dict):
   if x.get('mathdb_id') in {r['record']['mathdb_id'] for r in rows}:hits.append(x)
   else:
    for v in x.values():visit(v)
  elif isinstance(x,list):
   for v in x:visit(v)
 visit(data);print('exact ID hits',json.dumps(hits,ensure_ascii=False))
print('UPSTREAM',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json').read_text())
print('CONTEXT', (B/'prior-campaign-context.json').read_text()[:5000])
print('LEDGER', (B/'ledger.json').read_text()[:4000])
