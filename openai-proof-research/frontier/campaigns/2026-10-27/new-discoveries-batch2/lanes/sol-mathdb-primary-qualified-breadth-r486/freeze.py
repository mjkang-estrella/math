from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent; L=O.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r485'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def ref(p):
 d=p.read_bytes();return dict(path=str(p.resolve()),sha256=hashlib.sha256(d).hexdigest(),size=len(d))
def check(p,e):
 r=ref(p);assert r['sha256']==e['sha256'] and r['size']==e.get('size',e.get('bytes')),str(p);return r
refs=load(O/'initial-bindings.json')
m=load(I/'manifest.json'); listed={e['path'] for e in m['files']};actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert actual==listed
for e in m['files']:refs.append(check(I/e['path'],e))
for e in load(I/'bindings.json'):
 for k in ['original','copy']:refs.append(check(Path(e[k]),e))
cm=load(C/'manifest.json'); chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:refs.append(check(C/e['path'],e))
admin=[]
for lane in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 for p in (L/lane).glob('*'):
  if p.is_file():refs.append(ref(p));admin.append(p)
for p in [B/'ledger.json',B/'prior-campaign-context.json']:refs.append(ref(p))
refs.append(ref(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'))
refs=list({r['path']:r for r in refs}.values());(O/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
r=load(I/'reserved-ids.json');q=load(I/'queue.json'); ids=set(r['ids']);other=r['other_active_reservations'];assert len(ids)==len(q)==50 and ids=={v['mathdb_id'] for v in q};assert len(other)==len(set(other))==100 and not ids.intersection(other);assert not ids.intersection({372627,372628,368940,404067,364119})
assert len(load(I/'coverage-delta.json'))==3383
rows=[]
for e in chunks:
 for n,line in enumerate((C/e['path']).open(),1):
  x=json.loads(line)
  if x.get('id',x.get('mathdb_id')) in ids:rows.append(dict(record=x,chunk=str((C/e['path']).resolve()),line=n))
assert len(rows)==50
(O/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(O/'freeze-receipt.json').write_text(json.dumps(dict(intake_payloads=len(listed),direct_bindings=len(load(I/'bindings.json')),original_corpus_chunks=20,frozen_inputs=8,flat_references=len(refs),own=50,other=100,baseline=3383,status='PASS'),indent=2)+'\n')
print((O/'freeze-receipt.json').read_text())
for p in admin:
 if p.name in ['README.md','DECISION.md','adjudications.json']: print(str(p),p.read_text()[:6000])
for p in [B/'ledger.json',B/'prior-campaign-context.json']: print(str(p),p.read_text()[:2200])
for row in rows:
 x=row['record'];print('\nRECORD',x.get('id',x.get('mathdb_id')),json.dumps(x,ensure_ascii=False))
