from pathlib import Path
import json
P=Path(__file__).resolve().parent;L=P.parent;B=L.parent
ids={d['mathdb_id'] for d in json.loads((P/'assigned-records.json').read_text())}
def scan(x,path=''):
 if isinstance(x,dict):
  s=json.dumps(x,ensure_ascii=False)
  if any(str(i) in s for i in ids) and len(s)<5000:print(path,s)
  else:
   for k,v in x.items():scan(v,path+'/'+k)
 elif isinstance(x,list):
  for n,v in enumerate(x):scan(v,path+'/'+str(n))
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',B/'ledger.json',B/'prior-campaign-context.json']:print('CONTEXT',str(p));scan(json.loads(p.read_text()))
print('RELATED ACCEPTED',json.dumps([r for r in json.loads((B/'ledger.json').read_text())['accepted'] if r['number']==35],ensure_ascii=False))
