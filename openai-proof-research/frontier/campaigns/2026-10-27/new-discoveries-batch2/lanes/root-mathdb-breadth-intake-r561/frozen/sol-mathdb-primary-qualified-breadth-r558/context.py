exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("m=json.loads")[0])
for name in ['ledger.json','prior-campaign-context.json']:
 x=json.loads((L.parent/name).read_text());print(name,str(x)[:7500])
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print(rel,(L/rel).read_text()[:13000])
for r in json.loads((D/'assigned-records.json').read_text()):
 x=r['record'];print(x['mathdb_id'],x['source_name'],x['source_url'],x['references'])
