from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-stack-park-intake-r531'
def h(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
paths=list(I.rglob('*')); paths=[p for p in paths if p.is_file()]
# Bind bytes before parsing any intake scientific/administrative payload.
a=[h(p) for p in sorted(paths)]
(D/'initial-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
m=json.loads((I/'manifest.json').read_text()); print('manifest keys',m.keys())
for e in m['files']:
 x=h(I/e['path']);assert all(x[k]==e[k] for k in ['sha256','size']),e
assert {str(p.relative_to(I)) for p in paths}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
b=json.loads((I/'bindings.json').read_text())
for e in b:
 for key in ['original','copy']:
  x=h(Path(e[key]));assert all(x[k]==e[k] for k in ['sha256','size']),e
  a.append(x)
(D/'initial-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
print('payload',len(m['files']),'pairs',len(b))
for name in ['queue.json','reserved-ids.json','active-breadth-reservations.json']:
 z=json.loads((I/name).read_text());print(name,json.dumps(z,ensure_ascii=False)[:14000])
inv=L/'pi-mathdb-full-corpus-inventory-r301'/'manifest.json';print('inventory',str(inv));print(inv.read_text()[:7000])
cm=json.loads(inv.read_text());assert h(inv)==h(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')|{'path':str(inv)}
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:
 p=inv.parent/e['path'];x=h(p);assert x['size']==e.get('size',e.get('bytes')) and x['sha256']==e['sha256'];a.append(x)
for e in json.loads((L/'sol-mathdb-stack-fiber-preliminary-review-r528/flat-bindings.json').read_text()):
 x=h(Path(e['path']));assert x['size']==e.get('size',e.get('bytes')) and x['sha256']==e['sha256'];a.append(x)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']+list(L.glob('*r304/accepted-exclusions.json'))+list(L.glob('*r304/historical-dispositions.json'))+list(L.glob('*r363/*')):
 if p.is_file():a.append(h(p))
unique={e['path']:e for e in a};(D/'flat-bindings.json').write_text(json.dumps(list(unique.values()),indent=2)+'\n')
cov=json.loads((I/'coverage-delta.json').read_text());assert len(cov)==4233
seen=set()
for r in json.loads((I/'active-breadth-reservations.json').read_text()):
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
print('ALL originals/chunks/inputs and disjointness PASS',len(unique))
rows=[];ids=set(json.loads((I/'reserved-ids.json').read_text())['ids'])
for e in chunks:
 p=inv.parent/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('mathdb_id',r.get('id')) in ids:rows.append({'chunk':str(p),'line':n,'record':r})
print('records',len(rows));(D/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(rows[0],ensure_ascii=False))
