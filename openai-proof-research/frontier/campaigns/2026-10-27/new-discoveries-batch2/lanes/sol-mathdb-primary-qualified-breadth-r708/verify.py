#!/usr/bin/env python3
"""Independent read-only verification. Invoke using the fixed helper guard."""
from pathlib import Path
import json,hashlib,sys,tempfile
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r707';R=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def sha(d):return hashlib.sha256(d).hexdigest()
def ck(p,h,n):
 d=p.read_bytes();assert len(d)==n,'size mismatch: '+str(p);assert sha(d)==h,'hash mismatch: '+str(p)
def payload(base,m):
 expected={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
 actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}
 assert actual==expected,'payload extra/missing: '+str(actual^expected)
 for x in m['files']:ck(base/x['path'],x['sha256'],x['size'])
def negatives():
 # Only tiny temporary fixtures in this lane; never mutate an original.
 with tempfile.TemporaryDirectory(prefix='.negative-',dir=O) as td:
  p=Path(td);(p/'a').write_bytes(b'abc');m={'files':[{'path':'a','sha256':sha(b'abc'),'size':3}],'excluded_exact_paths':[]};payload(p,m)
  tested=[]
  for name,data in [('hash',b'abd'),('size',b'abcd')]:
   (p/'a').write_bytes(data)
   try:payload(p,m)
   except AssertionError as e:assert name in str(e);tested.append(name)
   else:raise AssertionError('negative accepted: '+name)
  (p/'a').write_bytes(b'abc');(p/'extra').write_bytes(b'x')
  try:payload(p,m)
  except AssertionError as e:assert 'payload' in str(e);tested.append('extra-file')
  else:raise AssertionError('extra accepted')
 return tested
try:
 # Fixed externally observed intake manifest anchor, not a self-asserted upstream receipt.
 ck(I/'manifest.json','8175880d19229d8264f232281d826d5238781c52f2f0fb6daf1af2401a7fef73',10858)
 payload(I,j(I/'manifest.json'))
 bindings=j(O/'flat-bindings.json')
 for x in bindings:ck(Path(x['path']),x['sha256'],x['size'])
 for x in j(I/'bindings.json'):
  for k in ['original','copy']:ck(Path(x[k]),x['sha256'],x['bytes'])
 rm=j(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for x in chunks+rm['frozen_inputs']:ck(R/x['path'],x['sha256'],x['bytes'])
 cov=j(I/'coverage-delta.json');assert len(cov)==8583
 active=j(I/'active-breadth-reservations.json');assert len(active)==3
 seen=set()
 for x in active:
  ids=set(x['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(x['protected_ids']);seen|=ids
 res=j(I/'reserved-ids-r708.json');q=j(I/'queue-r708.json');ids=res['ids'];assert len(ids)==50 and [x['mathdb_id'] for x in q]==ids and any(x['ids']==ids for x in active)
 lit=j(O/'literal-records.json');disp=j(O/'dispositions.json');assert len(lit)==len(disp)==50 and {x['record']['mathdb_id'] for x in lit}==set(ids) and {x['mathdb_id'] for x in disp}==set(ids)
 found={}
 for x in chunks:
  p=R/x['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found
    found[r['mathdb_id']]=(r,str(p),n)
 assert set(found)==set(ids)
 for x in lit:
  r=x['record'];i=r['mathdb_id'];original,path,n=found[i];assert r==original and x['chunk']==path and x['line']==n
  h=sha(json.dumps(original,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert x['canonical_record_sha256']==h
  d=next(y for y in disp if y['mathdb_id']==i)
  assert d['canonical_record_sha256']==h and d['statement']==original['statement'] and d['statement_utf8_sha256']==sha(original['statement'].encode())
  assert d['corpus_chunk']==path and d['corpus_line']==n
  assert d['literal_classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and d['classification_reason'] and d['quantifiers'] and d['technical_assessment']
 assert len(j(O/'proposals.json'))<=3
 for x in j(O/'source-provenance.json'):
  for k in ['pdf','text']:
   if k in x:
    a=x[k];ck(Path(a['path']),a['sha256'],a['size'])
 m=j(O/'manifest.json');payload(O,m)
 receipt=O/'final-verification-receipt.json'
 if receipt.exists():
  a=j(receipt)['manifest'];ck(O/'manifest.json',a['sha256'],a['size'])
 tests=negatives() if '--self-test' in sys.argv else []
 print(json.dumps({'integrity':'PASS','intake_files':len(j(I/'manifest.json')['files']),'direct_pairs':46,'original_chunks':20,'frozen_inputs':8,'baseline':8583,'disjoint_reservations':3,'literal_records':50,'output_files':len(m['files']),'negative_tests':tests,'math_novelty':'NOT CLEARED'}))
except Exception as e:
 print('VERIFICATION FAILED: '+repr(e),file=sys.stderr);sys.exit(1)
