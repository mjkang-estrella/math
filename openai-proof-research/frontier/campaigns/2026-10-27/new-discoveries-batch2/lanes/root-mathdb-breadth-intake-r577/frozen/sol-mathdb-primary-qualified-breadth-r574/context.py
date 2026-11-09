import pathlib,json
P=pathlib.Path(__file__).parent;L=P.parent;B=L.parent
ids={x['record']['mathdb_id'] for x in json.loads((P/'assigned-records.json').read_text())}
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 v=json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text());print(n, 'top-level',type(v).__name__)
 print(json.dumps(v,ensure_ascii=False)[:2500]);print('assigned ID matches',[i for i in ids if str(i) in json.dumps(v)])
print((L/'root-mathdb-breadth-intake-r573/hypothesis-queue.json').read_text())
# Retain direct ledger/context scope without reproducing historical trees.
for n in ['ledger.json','prior-campaign-context.json']:
 v=json.loads((B/n).read_text());print(n)
 for a in v.get('accepted',[]):print(a.get('number'),a.get('mathdb_id',a.get('mathdb_related_id',a.get('related_mathdb_id'))),a.get('title'),a.get('scope',a.get('source_target')))
