exec(open(__file__.replace('context.py','bind.py')).read().split("q=load(I/'queue.json')")[0])
ids=set(load(I/'reserved-ids.json')['ids'])
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 data=load(p);print(p.name,'type',type(data).__name__)
 def walk(x):
  if isinstance(x,dict):
   if any(str(i)==str(v) for i in ids for k,v in x.items() if k in ('id','mathdb_id')): print(json.dumps(x,ensure_ascii=False)[:2500]);return
   for k,v in x.items():
    if k in map(str,ids):print(k,str(v)[:1600])
    else:walk(v)
  elif isinstance(x,list):
   for y in x:walk(y)
 walk(data)
print((L/'root-mathdb-cayley-review-intake-r363/DECISION.md').read_text())
