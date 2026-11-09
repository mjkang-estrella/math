from pathlib import Path
import json,hashlib,sys
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r635';R=L/'pi-mathdb-full-corpus-inventory-r301'
def js(p):return json.loads(Path(p).read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,h,s):
 b=Path(p).read_bytes();assert len(b)==s,('size',str(p));assert digest(b)==h,('hash',str(p))
def payload(root,m,mode=None):
 excluded=set(m['excluded_exact_paths']);assert excluded=={'manifest.json','final-verification-receipt.json'} if root==O else excluded=={'manifest.json','verification-receipt.json'}
 files={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert not any(p.is_symlink() for p in root.rglob('*'))
 if mode=='extra':files.add('__negative_virtual_extra__')
 assert files-set(excluded)=={x['path'] for x in m['files']},('extra/missing',str(root))
 for n,x in enumerate(m['files']):
  b=(root/x['path']).read_bytes()
  if n==0 and mode=='hash':b=bytes([b[0]^1])+b[1:]
  if n==0 and mode=='size':b+=b'X'
  assert len(b)==x['size'],('payload size',x['path'])
  assert digest(b)==x['sha256'],('payload hash',x['path'])
def verify(mode=None):
 m=js(O/'manifest.json');payload(O,m,mode)
 for x in js(O/'initial-bindings.json'):check(x['path'],x['sha256'],x['size'])
 for x in js(O/'flat-bindings.json'):check(x['path'],x['sha256'],x['size'])
 im=js(I/'manifest.json');payload(I,im)
 pairs=js(I/'bindings.json')
 for x in pairs:
  for key in ['original','copy']:check(x[key],x['sha256'],x['bytes'])
 inv=js(R/'manifest.json');chunks=[x for x in inv['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for x in chunks+inv['frozen_inputs']:check(R/x['path'],x['sha256'],x['bytes'])
 coverage=js(I/'coverage-delta.json');assert len(coverage)==6783
 active=js(I/'active-breadth-reservations.json');assert len(active)==3
 seen=set(map(int,coverage));reserved=js(I/'reserved-ids-r636.json');queue=js(I/'queue-r636.json');ids={x['mathdb_id'] for x in queue};assert len(ids)==50
 # Reservation is an explicitly scoped object.
 assert set(reserved['ids'])==ids and reserved['coverage_baseline']==6783 and reserved['lane']==O.name and not reserved['active_hypothesis_ids']
 for a in active:
  s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(a['protected_ids']) and not a['active_hypothesis_ids'];seen|=s
 assert set(next(a for a in active if a['lane']==O.name)['ids'])==ids
 rows=js(O/'literal-records.json');ds=js(O/'dispositions.json');assert len(rows)==len(ds)==50 and {x['record']['mathdb_id'] for x in rows}==ids and {x['mathdb_id'] for x in ds}==ids
 found={}
 for x in chunks:
  p=R/x['path']
  for ln,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r.get('mathdb_id') in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),ln,r)
 assert set(found)==ids
 for x in rows:
  r=x['record'];p,ln,actual=found[r['mathdb_id']];assert r==actual and x['chunk']==p and x['line']==ln
  h=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert x['canonical_record_sha256']==h
  d=next(a for a in ds if a['mathdb_id']==r['mathdb_id']);assert d['statement']==r['statement'] and d['statement_utf8_sha256']==digest(r['statement'].encode()) and d['canonical_record_sha256']==h and d['corpus_chunk']==p and d['corpus_line']==ln and d['literal_review_complete'] and d['accepted_credit']==0
 assert js(O/'proposals.json')==[]
 for x in js(O/'fetch-provenance.json')+js(O/'derivative-bindings.json'):
  if 'path' in x:check(O/x['path'],x['sha256'],x['size'])
 for x in js(O/'selected-passages.json'):
  t='\n'.join(Path(x['path']).read_text().splitlines()[x['start_line']-1:x['end_line']]);assert t==x['text'] and digest(t.encode())==x['text_sha256']
 return dict(integrity='PASS',literal_reviews=50,coverage_baseline=6783,proposals=0,original_chunks=20,frozen_inputs=8,direct_binding_pairs=len(pairs),reservation_disjointness=True,scientific_acceptance=False)
if __name__=='__main__':
 try:print(json.dumps(verify(sys.argv[1] if len(sys.argv)>1 else None),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
