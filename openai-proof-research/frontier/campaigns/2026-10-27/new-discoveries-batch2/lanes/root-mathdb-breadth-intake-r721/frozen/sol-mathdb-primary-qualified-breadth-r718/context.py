import json,pathlib
O=pathlib.Path(__file__).parent;L=O.parent;B=L.parent
for p in [L/'root-mathdb-breadth-intake-r717/adjudications.json',L/'root-mathdb-breadth-intake-r717/hypothesis-queue.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print(p.name,p.read_text())
ids={x['id'] for x in json.loads((O/'literal-records.json').read_text())}
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 data=json.loads(p.read_text());print(p.name,'top keys',list(data)[:20])
 def walk(v):
  if isinstance(v,dict):
   if any(str(i) in json.dumps(v) for i in ids) and len(json.dumps(v))<8000: print(json.dumps(v,ensure_ascii=False));return
   for w in v.values():walk(w)
  elif isinstance(v,list):
   for w in v:walk(w)
 walk(data)
