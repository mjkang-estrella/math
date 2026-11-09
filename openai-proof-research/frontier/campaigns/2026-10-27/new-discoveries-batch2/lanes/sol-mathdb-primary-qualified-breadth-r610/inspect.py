import json,pathlib
D=pathlib.Path(__file__).parent;rows=json.loads((D/'literal-records.json').read_text())
for i,x in enumerate(rows):
 r=x['record'];print(r['mathdb_id'],r['source_url'])
 if 18<=i<=30:print(r['statement'])
print((D.parent/'root-mathdb-cayley-review-intake-r363/DECISION.md').read_text())
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 o=json.loads((D.parent/'root-mathdb-accepted-exclusions-r304'/n).read_text());print(n,type(o).__name__,list(o)[:12])
