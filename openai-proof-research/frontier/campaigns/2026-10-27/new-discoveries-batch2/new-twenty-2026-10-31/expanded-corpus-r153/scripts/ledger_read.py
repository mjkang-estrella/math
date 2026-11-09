import json,pathlib
L=pathlib.Path(__file__).resolve().parents[1];p=L.parent/'ledger.json';d=json.loads(p.read_text());print('keys',list(d))
def walk(o):
 if isinstance(o,dict):
  if any(k in o for k in ['mathdb_id','mathdb_related_id','problem_id']):
   print({k:o[k] for k in ['mathdb_id','mathdb_related_id','problem_id','title','status','discovery_count_credit'] if k in o})
  for k,v in o.items():
   if not isinstance(v,(dict,list)) and k in ['accepted_count','target','target_new','target_additional']:print(k,v)
   if isinstance(v,(dict,list)):walk(v)
 elif isinstance(o,list):
  for v in o:walk(v)
walk(d)
