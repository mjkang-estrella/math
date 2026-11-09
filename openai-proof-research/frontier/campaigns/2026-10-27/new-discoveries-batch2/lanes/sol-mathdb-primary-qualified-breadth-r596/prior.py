import json,pathlib
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent;ids={r['record']['mathdb_id'] for r in json.loads((L/'literal-records.json').read_text())}
for n in ['ledger.json','prior-campaign-context.json']:
 v=json.loads((B/n).read_text());print(n,json.dumps(v,ensure_ascii=False)[:4500])
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 v=json.loads((L.parent/'root-mathdb-accepted-exclusions-r304'/n).read_text());print(n,'schema',str(v)[:1000]);print('assigned matches',[(i,str(i) in json.dumps(v)) for i in ids if str(i) in json.dumps(v)])
