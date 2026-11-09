"""Read-only independent verifier. Run via verify.sh; no upstream code executed."""
from pathlib import Path
import json,hashlib,sys
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r633';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check_bytes(b,e):
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch')
 if h(b)!=e['sha256']:raise ValueError('hash mismatch')
def check(p,e):
 try:check_bytes(p.read_bytes(),e)
 except Exception as x:raise ValueError(str(p)+': '+str(x)) from x
def exact(root,m,inject=None):
 exclusions=m.get('excluded_exact_paths',[]);names=[e['path'] for e in m['files']]
 if len(names)!=len(set(names)):raise ValueError('duplicate manifest entries')
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if inject=='extra':actual.add('unlisted-negative-file')
 if actual!=set(names)|set(exclusions):raise ValueError('extra or missing file')
 for e in m['files']:
  b=(root/e['path']).read_bytes()
  if inject in ['hash','size']:
   if inject=='hash':b=bytes([b[0]^1])+b[1:] if b else b'x'
   else:b+=b'x'
   check_bytes(b,e)
  check_bytes(b,e)
def validate(inject=None):
 receipt=j(O/'final-verification-receipt.json')
 if not receipt.get('pending'):
  check(O/'manifest.json',{'sha256':receipt['manifest_sha256'],'size':receipt['manifest_size']})
 m=j(O/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(O,m,inject)
 for e in j(O/'initial-bindings.json'):check(Path(e['path']),e)
 for e in j(O/'flat-bindings.json'):check(Path(e['path']),e)
 for e in j(O/'cached-source-bindings.json')['references']:check(Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(Path(e[k]),e)
 inv=j(C/'manifest.json');check(C/'manifest.json',next(e for e in j(O/'flat-bindings.json') if e['path']==str(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')))
 chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==6733
 active=j(I/'active-breadth-reservations.json');assert len(active)==3;seen=set()
 for a in active:
  ids=set(a['ids']);assert len(a['ids'])==len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids
 assert len(seen)==150
 for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
 reservation=j(I/'reserved-ids-r634.json');ids=set(reservation['ids']);assert reservation['coverage_baseline']==6733 and reservation['lane']==O.name
 assert ids=={x['mathdb_id'] for x in j(I/'queue-r634.json')}
 ds=j(O/'dispositions.json');lit=j(O/'literal-records.json');assert len(ds)==len(lit)==50 and {x['mathdb_id'] for x in ds}==ids and {x['mathdb_id'] for x in lit}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 assert set(found)==ids
 for x in ds+lit:
  p,n,r=found[x['mathdb_id']];assert x['corpus_chunk']==p and x['corpus_line']==n
  assert x['statement_utf8']==r['statement'] and x['statement_utf8_sha256']==h(r['statement'].encode('utf8'))
  assert x['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8'))
  if 'record' in x:assert x['record']==r
 for d in ds:
  assert d['accepted_credit']==0 and d['evidence']['full_dependency_audit'] is False
 assert j(O/'proposals.json')==[]
 assert len((I/'routing-queue.jsonl').read_text().splitlines())==8000
 for e in j(O/'derivative-bindings.json'):check(O/e['path'],e)
 check(O/'selected-passages.json',j(O/'passage-bindings.json'))
 f=j(O/'fetch-provenance.json');check(O/f['path'],f)
 return {'integrity':'PASS','intake_payload_files':len(j(I/'manifest.json')['files']),'direct_original_copy_pairs':len(j(I/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'literal_reviews':50,'selected_primary_passages':46,'proposals':0,'baseline':6733,'disjoint_reserved_ids':150,'mathematical_acceptance':False,'novelty_clearance':False}
if __name__=='__main__':
 try:
  print(json.dumps(validate(sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None),sort_keys=True))
 except Exception as e:print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
