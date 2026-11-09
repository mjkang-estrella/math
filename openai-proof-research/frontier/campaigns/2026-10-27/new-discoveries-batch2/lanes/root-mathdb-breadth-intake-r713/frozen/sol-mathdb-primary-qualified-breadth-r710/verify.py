#!/usr/bin/env python3
"""Independent read-only verifier. Negative modes alter only in-memory bytes."""
from pathlib import Path
import hashlib,json,sys
P=Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r709';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def ck(p,sha,size):
 b=p.read_bytes();assert len(b)==size and h(b)==sha,'binding mismatch '+str(p)
def payload(entries,data):
 assert set(data)=={r['path'] for r in entries},'extra/missing payload'
 for r in entries:
  b=data[r['path']];assert len(b)==r['size'],'size mismatch '+r['path'];assert h(b)==r['sha256'],'hash mismatch '+r['path']
def verify():
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 data={str(p.relative_to(P)):p.read_bytes() for p in P.rglob('*') if p.is_file() and str(p.relative_to(P)) not in m['excluded_exact_paths']}
 if len(sys.argv)>1:
  k=next(iter(data))
  if sys.argv[1]=='--negative-hash':data[k]=bytes([data[k][0]^1])+data[k][1:]
  elif sys.argv[1]=='--negative-size':data[k]+=b' '
  elif sys.argv[1]=='--negative-extra':data['unexpected-extra']=b'x'
  else:raise ValueError('unknown argument')
 payload(m['files'],data)
 bindings=j(P/'flat-bindings.json')
 for r in bindings:ck(Path(r['path']),r['sha256'],r['size'])
 # The intake manifest and receipt themselves are bound above, not self-trusted.
 im=j(I/'manifest.json')
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={r['path'] for r in im['files']}|set(im['excluded_exact_paths'])
 for r in im['files']:ck(I/r['path'],r['sha256'],r['size'])
 pairs=j(I/'bindings.json')
 for r in pairs:
  for key in ['original','copy']:ck(Path(r[key]),r['sha256'],r['bytes'])
 cm=j(C/'manifest.json')
 chunks=[r for r in cm['files'] if r['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for r in chunks+cm['frozen_inputs']:ck(C/r['path'],r['sha256'],r['bytes'])
 active=j(I/'active-breadth-reservations.json');cov=j(I/'coverage-delta.json')
 assert len(cov)==8633 and len(active)==3
 seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50
  assert not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids'])
  seen|=ids
 res=j(I/'reserved-ids-r710.json');q=j(I/'queue-r710.json')
 ids=set(res['ids']);assert len(q)==50 and ids=={r['mathdb_id'] for r in q}
 ds=j(P/'dispositions.json');lit=j(P/'literal-records.json')
 assert len(ds)==len(lit)==50 and {d['mathdb_id'] for d in ds}==ids=={f['mathdb_id'] for f in lit}
 wanted={}
 for f in lit:wanted.setdefault(f['corpus_chunk'],{})[f['corpus_line']]=f
 actual={}
 for path,lines in wanted.items():
  for n,line in enumerate(Path(path).open(),1):
   if n in lines:
    f=lines[n];r=json.loads(line);assert r==f['record'];assert r['mathdb_id']==f['mathdb_id']
    sha=h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
    assert sha==f['canonical_record_sha256'];actual[f['mathdb_id']]=(r,sha,path,n)
 assert len(actual)==50
 for d in ds:
  r,sha,path,n=actual[d['mathdb_id']]
  assert d['corpus_chunk']==path and d['corpus_line']==n
  assert d['statement_utf8']==r['statement'] and d['statement_utf8_sha256']==h(r['statement'].encode())
  assert d['canonical_record_sha256']==sha
  assert d['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete']
  assert d['classification_reason_and_quantifiers'] and d['technical_assessment']
  assert d['accepted_credit']==0 and not d['registry_cleared']
 assert j(P/'proposals.json')==[]
 for r in j(P/'source-provenance.json'):
  ck(P/(r['version']+'.pdf'),r['sha256'],r['size'])
  ck(P/r['text']['path'],r['text']['sha256'],r['text']['size'])
 receipt=P/'final-verification-receipt.json'
 if receipt.exists():
  rr=j(receipt);ck(P/'manifest.json',rr['manifest_sha256'],rr['manifest_size'])
 return {'integrity':'PASS','literal_records':50,'original_chunks':20,'frozen_inputs':8,'reservation_sets':3,'baseline':8633,'proposals':0,'scientific_acceptance':False}
if __name__=='__main__':
 try:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
