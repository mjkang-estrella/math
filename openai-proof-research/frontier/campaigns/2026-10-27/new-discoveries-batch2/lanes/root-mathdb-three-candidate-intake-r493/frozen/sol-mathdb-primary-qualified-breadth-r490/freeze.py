from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent; L=O.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r489'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def ref(p):
 z=p.read_bytes();return dict(path=str(p),size=len(z),sha256=hashlib.sha256(z).hexdigest())
def check(p,r):
 a=ref(p);assert a['size']==r.get('size',r.get('bytes')) and a['sha256']==r['sha256'],str(p);return a
m=load(I/'manifest.json'); actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert actual=={r['path'] for r in m['files']}
refs=load(O/'initial-flat-bindings.json')
for r in m['files']:check(I/r['path'],r)
bindings=load(I/'bindings.json')
for r in bindings:
 for k in ['original','copy']:refs.append(check(Path(r[k]),r))
cm=load(C/'manifest.json');chunks=[r for r in cm['files'] if r['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for r in chunks+cm['frozen_inputs']:refs.append(check(C/r['path'],r))
reserved=load(I/'reserved-ids.json');ids=reserved['ids'];assert len(ids)==len(set(ids))==50 and set(ids)=={r['mathdb_id'] for r in load(I/'queue.json')};assert len(set(reserved['other_active_reservations']))==100 and not set(ids)&set(reserved['other_active_reservations']);assert not set(ids)&{372627,372628,368940,404067,364119}
# Direct frozen reservation inputs bind the two active allocations; do not recurse.
a=load(I/'frozen/root-mathdb-breadth-intake-r479/reserved-ids.json');s=load(I/'frozen/root-mathdb-breadth-intake-r487/reserved-ids.json');assert set(a['ids'])|set(s['ids'])==set(reserved['other_active_reservations']);assert not set(a['ids'])&set(s['ids'])
coverage=load(I/'coverage-delta.json');assert len(coverage)==3483 and not set(map(str,ids))&set(coverage)
rows=[]
for ch in chunks:
 p=C/ch['path']
 for line,z in enumerate(p.open(),1):
  r=json.loads(z)
  if r.get('id',r.get('mathdb_id')) in ids:
   rows.append(dict(record=r,original_chunk=str(p),original_line=line))
assert len(rows)==50
(O/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
refs={r['path']:r for r in refs};(O/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(O/'freeze-receipt.json').write_text(json.dumps(dict(status='PASS',intake_payloads=len(actual),direct_bindings=len(bindings),chunks=20,frozen_inputs=8,assigned=50,other_reserved=100,baseline=3483),indent=2)+'\n')
print('FREEZE PASS');print('record keys',rows[0]['record'].keys())
for x in rows:
 r=x['record'];print(json.dumps(r,ensure_ascii=False))
