from pathlib import Path
import json
D=Path(__file__).parent;L=D.parent;B=L.parent
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 a=json.loads(p.read_text());print(p.name,'type',type(a).__name__,'keys',list(a)[:15]);
 ids=[str(x['id']) for x in json.loads((D/'literal-records.json').read_text())]
 if isinstance(a,dict):
  for k,v in a.items():
   if k in ids:print(k,v)
print('selected metadata')
for a in json.loads((D/'literal-records.json').read_text()):
 if a['id'] in [391007,391096,391133,391123]:print(a['id'],a['record']['source_url'],a['record']['first_stated_year_source_url'])
