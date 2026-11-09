import json,pathlib
P=pathlib.Path(__file__).parent;L=P.parent
rows=json.loads((P/'assigned-records.json').read_text())
for r in rows:
 if r['mathdb_id'] in [349116,350616,355513,357365,356490,354537]:print(json.dumps(r['record'],ensure_ascii=False,indent=2))
for n in ['ledger.json','prior-campaign-context.json']:print(n,(L.parent/n).read_text()[:16000])
for p in L.glob('*r363*/DECISION.md'):print(str(p),p.read_text())
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 obj=json.loads((L/'pi-mathdb-full-corpus-inventory-r301/frozen/root-mathdb-accepted-exclusions-r304'/name).read_text());print(name,json.dumps(obj,ensure_ascii=False)[:14000])
