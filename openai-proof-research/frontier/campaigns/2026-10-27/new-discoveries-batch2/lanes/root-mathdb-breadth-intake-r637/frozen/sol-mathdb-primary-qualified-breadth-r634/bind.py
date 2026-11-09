from pathlib import Path
import json,hashlib,datetime
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r633';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def bind(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 a=bind(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p)
refs=j(O/'initial-bindings.json')
for e in refs:check(Path(e['path']),e)
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:check(I/e['path'],e);refs.append(bind(I/e['path']))
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(Path(e[k]),e);refs.append(bind(Path(e[k])))
for e in j(L/'sol-mathdb-primary-qualified-breadth-r630/flat-bindings.json'):
 check(Path(e['path']),e);refs.append(e)
check(C/'manifest.json',bind(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'))
v=j(C/'manifest.json');chunks=[e for e in v['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(v['frozen_inputs'])==8
for e in chunks+v['frozen_inputs']:check(C/e['path'],e);refs.append(bind(C/e['path']))
refs={e['path']:e for e in refs};(O/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
cov=j(I/'coverage-delta.json');assert len(cov)==6733
active=j(I/'active-breadth-reservations.json');seen=set()
for a in active:
 ids=set(a['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids
assert len(seen)==150
for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
ids=set(j(I/'reserved-ids-r634.json')['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r634.json')}
found=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:found.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'statement_utf8':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(found)==50 and {r['mathdb_id'] for r in found}==ids
(O/'literal-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
(O/'binding-check.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_payload_files':len(m['files']),'direct_original_copy_pairs':len(j(I/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'flat_references':len(refs),'coverage_baseline':6733,'disjoint_reservations':150,'records':50,'upstream_verifier_executed':False},indent=2)+'\n')
print('bound all inputs; records ready')
