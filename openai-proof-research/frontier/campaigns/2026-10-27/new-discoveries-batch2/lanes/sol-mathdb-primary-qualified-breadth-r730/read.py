import json,pathlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent
for name in ['ledger.json','prior-campaign-context.json']:
 x=json.loads((B/name).read_text());print(name,json.dumps(x,ensure_ascii=False)[:5500])
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-breadth-intake-r729/adjudications.json',L/'root-mathdb-breadth-intake-r729/hypothesis-queue.json']:
 print(p.name,p.read_text()[:13000])
rows=json.loads((P/'literal-records.json').read_text())
for i,r in enumerate(rows):
 if 22<=i<=29:print(i,r['record']['mathdb_id'],r['record']['statement'])
print('ALL ORDER',[(i,r['record']['mathdb_id']) for i,r in enumerate(rows)])
