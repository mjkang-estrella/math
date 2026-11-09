"""Independent read-only validation. Run only through the specified helper guard."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r555';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size: {p}';assert h(b)==e['sha256'],f'hash: {p}'
def exact(root,m):
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names)),'duplicate manifest name'
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==set(names)|set(m['excluded_exact_paths']),'extra/missing file'
 for e in m['files']:check(root/e['path'],e)
def verify():
 m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'};exact(P,m)
 refs=j(P/'flat-bindings.json');assert len(refs)==len({r['path'] for r in refs})
 for r in refs:check(pathlib.Path(r['path']),r)
 # Recheck exact upstream intake payload, original/copy byte identities and inventory itself.
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 frozen=I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'
 assert (C/'manifest.json').read_bytes()==frozen.read_bytes()
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4833
 reservations=j(I/'active-breadth-reservations.json');seen=set()
 for r in reservations:
  s=set(r['ids']);assert len(s)==len(r['ids'])==50
  assert not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
 assert len(seen)==150
 for r in reservations:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 res=j(I/'reserved-ids.json');assert res['lane']==P.name
 ids=set(res['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue.json')}
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 assert len(found)==50
 assigned={r['mathdb_id']:r for r in j(P/'assigned-records.json')};assert len(assigned)==50
 for d in ds:
  p,n,r=found[d['mathdb_id']]
  assert d['chunk']==str(p) and d['line']==n and d['statement']==r['statement']
  assert d['statement_sha256']==h(r['statement'].encode('utf-8'))
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  assert assigned[d['mathdb_id']]['record']==r
  assert d['literal_statement_read'] and d['reason'] and d['accepted_credit']==0 and not d['current_registry_cleared']
 assert j(P/'proposals.json')==[]
 for e in j(P/'downloads.json'):
  if 'path' in e:check(pathlib.Path(e['path']),e)
 for e in j(P/'derivative-bindings.json'):check(pathlib.Path(e['path']),e)
 return {'integrity':'PASS','literal_reviews':50,'original_chunks':20,'frozen_inputs':8,'baseline':4833,'reserved_total':150,'flat_references':len(refs),'proposals':0,'scientific_acceptance':False,'novelty_clearance':False}
if __name__=='__main__':
 try:
  if len(sys.argv)==3 and sys.argv[1]=='--payload-only':
   p=pathlib.Path(sys.argv[2]);exact(p,j(p/'manifest.json'));print('fixture payload PASS')
  else:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print(f'FAIL: {type(e).__name__}: {e}',file=sys.stderr);sys.exit(1)
