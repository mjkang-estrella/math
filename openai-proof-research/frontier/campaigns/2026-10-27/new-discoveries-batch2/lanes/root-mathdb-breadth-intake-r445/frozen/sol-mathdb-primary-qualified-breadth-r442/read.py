from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent;A=L/'root-mathdb-breadth-intake-r441';I=L/'pi-mathdb-full-corpus-inventory-r301'
a=json.loads((A/'reserved-ids.json').read_text());ids=set(map(str,a['ids']));old=json.loads((A/'coverage-delta.json').read_text());assert len(ids)==50 and len(old)==2433 and not ids&set(old) and not ids&set(map(str,a['other_active_reservations'])) and not ids&{'372627','372628','368940','404067','364119'}
found={}
for e in json.loads((I/'manifest.json').read_text())['files']:
 if not e['path'].startswith('corpus/'):continue
 for line in (I/e['path']).open():
  x=json.loads(line);n=str(x['mathdb_id'])
  if n in ids:assert n not in found;found[n]=x
assert set(found)==ids
rows=[found[str(n)] for n in a['ids']];(R/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
with (R/'statements.txt').open('w') as f:
 for x in rows:f.write(str(x['mathdb_id'])+' '+x['title']+'\n'+x['statement']+'\n\n')
print((R/'statements.txt').read_text());print('ASSIGNED KEYS',list(rows[0]))
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/disposition.json']:
 d=json.loads(p.read_text());print('ADMIN',str(p),json.dumps(d)[:1000])
