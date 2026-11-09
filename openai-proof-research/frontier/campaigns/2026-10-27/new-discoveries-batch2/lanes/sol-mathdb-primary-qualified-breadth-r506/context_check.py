from pathlib import Path
import json,re
O=Path(__file__).parent;L=O.parent;B=L.parent
ids={x['record']['mathdb_id'] for x in json.loads((O/'assigned-records.json').read_text())}
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',B/'ledger.json',B/'prior-campaign-context.json']:
 x=json.loads(p.read_text());print(p.name,'keys',list(x));
 def walk(x):
  if isinstance(x,dict):
   if any(str(i) in json.dumps(x) for i in ids) and len(json.dumps(x))<15000:print(json.dumps(x,ensure_ascii=False))
   else:
    for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(x)
 if p.name=='accepted-exclusions.json':print('family scopes',[(f['title'],f['scope']) for f in x['families']])
