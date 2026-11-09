from pathlib import Path
import json
L=Path(__file__).parent;B=L.parent.parent
for name in ['accepted-exclusions','historical-dispositions']:
 x=json.loads((L.parent/'root-mathdb-accepted-exclusions-r304'/(name+'.json')).read_text())
 for k,v in x.items():
  if isinstance(v,list):
   for r in v:
    if not isinstance(r,dict):continue
    print(name,k,json.dumps({a:b for a,b in r.items() if a in ['number','title','scope','mathdb_id','mathdb_ids','reason','id','status']},ensure_ascii=False))
for n in ['ledger.json','prior-campaign-context.json']:
 x=json.loads((B/n).read_text()); print(n,'keys',list(x) if isinstance(x,dict) else len(x))
