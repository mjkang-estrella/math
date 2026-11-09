"""Independent read-only verifier. Run through the fixed helper_guard.py with python3 -B."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r551';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}';assert h(b)==e['sha256'],f'hash mismatch: {p}'
def exact(root,m):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 assert actual==names,'extra or missing file'
 for e in m['files']:check(root/e['path'],e)
def validate():
 exact(P,j(P/'manifest.json'))
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 check(C/'manifest.json',{'sha256':h((I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()),'size':(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').stat().st_size})
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 r=j(I/'reserved-ids.json');ids=set(r['ids']);assert len(ids)==50 and r['lane']==P.name
 assert ids=={x['mathdb_id'] for x in j(I/'queue.json')}
 cov=j(I/'coverage-delta.json');assert len(cov)==4733;covered=set(map(int,cov));seen=set()
 for a in j(I/'active-breadth-reservations.json'):
  s=set(a['ids']);assert len(s)==50 and not s&(seen|covered|set(r['protected_ids']));seen|=s
 assert seen==ids|set(r['other_active_reservations']) and len(seen)==150
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   rec=json.loads(line)
   if rec['mathdb_id'] in ids:
    assert rec['mathdb_id'] not in found;found[rec['mathdb_id']]=(p,n,rec)
 assert len(found)==50
 ar=j(P/'assigned-records.json');assert len(ar)==50 and {d['mathdb_id'] for d in ar}==ids
 for d in ds+ar:
  p,n,rec=found[d['mathdb_id']];assert d['chunk']==str(p) and d['line']==n and d['statement']==rec['statement']
  assert d['statement_sha256']==h(rec['statement'].encode())
  assert d['canonical_record_sha256']==h(json.dumps(rec,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  if 'record' in d:assert d['record']==rec
  else:assert d['literal_full_statement_read'] and d['accepted_credit']==0 and not d['current_registry_cleared']
 assert j(P/'proposals.json')==[]
 for e in j(P/'downloads.json')+j(P/'derivative-bindings.json'):
  if 'path' in e:check(P/e['path'],e)
 return {'integrity':'PASS','literal_reviews':50,'chunks':20,'frozen_inputs':8,'active_reservations':150,'proposals':0,'math_novelty':'NOT_CLEARED'}
if __name__=='__main__':
 try:print(json.dumps(validate(),sort_keys=True))
 except Exception as ex:print(type(ex).__name__+': '+str(ex),file=sys.stderr);sys.exit(1)
