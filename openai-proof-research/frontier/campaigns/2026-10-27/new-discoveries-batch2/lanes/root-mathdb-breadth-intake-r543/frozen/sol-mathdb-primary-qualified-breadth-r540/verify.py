#!/usr/bin/env python3
"""Independent read-only validation. Never imports or executes upstream verifier."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r539';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch {p}'
 assert h(b)==e['sha256'],f'hash mismatch {p}'
def exact(root,m,negative=None):
 assert set(m['excluded_exact_paths'])=={'manifest.json','verification-receipt.json'}
 names={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if negative=='extra':names.add('virtual-unlisted-negative-file')
 assert len(m['files'])==len({e['path'] for e in m['files']})
 assert names=={e['path'] for e in m['files']},f'extra/missing file {root}'
 for n,e in enumerate(m['files']):
  if n==0 and negative in {'hash','size'}:
   e=dict(e)
   if negative=='hash':e['sha256']='0'*64
   else:e['size']+=1
  check(root/e['path'],e)
def validate():
 negative=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
 assert negative in {None,'hash','size','extra'}
 exact(P,j(P/'manifest.json'),negative)
 # Original initial bindings anchor intake manifest and receipt before scientific reads.
 lines=(P/'initial-sha256.txt').read_text().splitlines()
 for line in lines:
  digest,path=line.split(maxsplit=1);assert h(pathlib.Path(path).read_bytes())==digest
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 assert (C/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==4433
 active=j(I/'active-breadth-reservations.json');seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==len(r['ids'])==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
 assert len(seen)==150
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 res=j(I/'reserved-ids.json');assert res['lane']==P.name and res['coverage_baseline']==4433
 ids=set(res['ids']);assert len(ids)==50 and ids=={r['mathdb_id'] for r in j(I/'queue.json')}
 assert any(r==res for r in active)
 ds=j(P/'dispositions.json');a=j(P/'assigned-records.json');assert len(ds)==len(a)==50 and {d['mathdb_id'] for d in ds}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 assert len(found)==50
 for d in ds+a:
  p,n,r=found[d['mathdb_id']]
  assert d['corpus_chunk']==str(p) and d['corpus_line_1based']==n
  assert d['statement']==r['statement'] and d['statement_utf8_sha256']==h(r['statement'].encode('utf8'))
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8'))
  if 'record' in d:assert d['record']==r
  else:assert d['credit']==0 and d['literal_full_statement_read'] and not d['current_registry_cleared'] and d['technical_review']
 assert j(P/'proposals.json')==[]
 for n in ['download-bindings.json','derivative-bindings.json']:
  for e in j(P/n):
   if 'path' in e:check(P/e['path'],e)
 print(json.dumps({'integrity':'PASS','literal_reviews':50,'proposals':0,'corpus_chunks':20,'frozen_inputs':8,'active_reserved':150,'scientific_acceptance':False}))
if __name__=='__main__':
 try:validate()
 except Exception as e:print(f'FAIL: {type(e).__name__}: {e}',file=sys.stderr);sys.exit(1)
