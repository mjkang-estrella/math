import json,pathlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 d=json.loads((L/rel).read_text());print(rel,'type',type(d).__name__,'keys',list(d)[:15] if isinstance(d,dict) else len(d))
 print(json.dumps(d,ensure_ascii=False)[:1800])
for f in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L.parent/f).read_text());print(f,'keys',list(d)[:12])
