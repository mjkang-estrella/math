import pathlib,json
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent
for n in ['adjudications.json','hypothesis-queue.json']:
 print(n,(L/'root-mathdb-breadth-intake-r719'/n).read_text())
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print(p.name,p.read_text()[:18000])
for n in ['ledger.json','prior-campaign-context.json']:
 x=json.loads((B/n).read_text());print(n, json.dumps(x,ensure_ascii=False)[:10000])
rs=json.loads((P/'literal-records.json').read_text())
for e in rs[20:27]:print(e['record']['mathdb_id'],e['record']['statement'])
