import pathlib,json
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 x=json.loads(p.read_text());print('\nFILE',p.name)
 def walk(x):
  if isinstance(x,dict):
   if any(k in x for k in ['scope','blocking_gates','record_associations']):print(json.dumps({k:v for k,v in x.items() if k in ['id','title','scope','status','blocking_gates','record_associations']},ensure_ascii=False))
   for k,v in x.items():
    if isinstance(v,(list,dict)):walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(x)
