import json,pathlib,hashlib
O=pathlib.Path(__file__).parent
for x in json.loads((O/'literal-records.json').read_text()):
 r=x['record'];print(r['mathdb_id'],r['statement'], '\nSOURCE',r['source_url'])
L=O.parent;I=L/'root-mathdb-breadth-intake-r667';c=json.loads((I/'coverage-delta.json').read_text());a=json.loads((I/'active-breadth-reservations.json').read_text());assert len(c)==7583
for s in a:assert not set(s['ids'])&set(map(int,c))
print('DISJOINT PASS coverage',len(c))
for p in [L/'root-mathdb-cayley-review-intake-r363'/'DECISION.md',I/'adjudications.json',I/'hypothesis-queue.json',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 print(p.name,p.read_text()[:14000])
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 d=json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text());print(n,'type',type(d).__name__,'keys',list(d)[:15])
