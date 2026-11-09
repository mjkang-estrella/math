#!/usr/bin/env python3
"""Independent read-only verifier. Run under the fixed helper_guard.py; writes nothing."""
from pathlib import Path
import hashlib,json,sys,datetime
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r575';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size',str(p));assert digest(b)==e['sha256'],('hash',str(p))
def payload(root,m,excluded):
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}; expected={e['path'] for e in m['files']};assert len(expected)==len(m['files']);assert actual==expected|set(excluded),('payload',sorted(actual^(expected|set(excluded))))
 for e in m['files']:check(root/e['path'],e)
def main():
 m=load(D/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];payload(D,m,m['excluded_exact_paths'])
 for e in load(D/'flat-bindings.json'):check(Path(e['path']),e)
 im=load(I/'manifest.json');payload(I,im,im['excluded_exact_paths'])
 for e in load(I/'bindings.json'):
  for k in ['original','copy']:check(Path(e[k]),e)
 check(R/'manifest.json',next(e for e in im['files'] if e['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'))
 rm=load(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
 reservation=load(I/'reserved-ids.json');ids=set(reservation['ids']);assert len(ids)==50 and reservation['lane']==D.name
 q=load(I/'queue.json');assert len(q)==50 and {x['mathdb_id'] for x in q}==ids
 coverage=set(map(int,load(I/'coverage-delta.json')));assert len(coverage)==5333
 sets=[set(x['ids']) for x in load(I/'active-breadth-reservations.json')];assert len(sets)==3 and ids in sets
 protected=set(reservation['protected_ids'])|{337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439}
 for j,s in enumerate(sets):
  assert len(s)==50 and not s&coverage and not s&protected
  for t in sets[:j]:assert not s&t
 assert set(reservation['other_active_reservations'])==set.union(*[s for s in sets if s!=ids])
 records={}
 for e in chunks:
  p=R/e['path']
  for ln,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in records;records[r['mathdb_id']]=(r,str(p),ln)
 assert set(records)==ids
 literals=load(D/'literal-records.json');dis=load(D/'dispositions.json');assert len(literals)==len(dis)==50 and {r['mathdb_id'] for r in literals}=={r['mathdb_id'] for r in dis}==ids
 for x in literals+dis:
  r,p,ln=records[x['mathdb_id']];assert x['statement']==r['statement'] and x['chunk']==p and x['line']==ln
  assert x['statement_sha256']==digest(r['statement'].encode())
  assert x['canonical_record_sha256']==digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  if 'record' in x:assert x['record']==r
 for x in dis:assert x['accepted_credit']==0 and not x['novelty_cleared'] and not x['full_dependencies_audited']
 assert len(load(D/'proposals.json'))<=3
 for e in load(D/'source-provenance.json'):
  if 'path' in e:check(Path(e['path']),e)
 for e in load(D/'derivative-bindings.json'):check(Path(e['path']),e)
 for x in load(D/'selected-passages.json'):
  t=(D/x['source']).read_text();assert t[x['start']:x['end']]==x['passage']
 tests=load(D/'negative-tests.json');assert all(tests[k] for k in ['hash_rejected','size_rejected','extra_file_rejected'])
 return dict(integrity='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=digest((D/'manifest.json').read_bytes()),manifest_size=(D/'manifest.json').stat().st_size,record_reviews=50,baseline_record_reviews=5333,original_chunks_verified=20,frozen_inputs_verified=8,direct_original_copy_pairs_verified=len(load(I/'bindings.json')),flat_references_verified=len(load(D/'flat-bindings.json')),negative_tests='PASS',mathematical_status='No new full-scope result established',novelty='HOLD',count_change=0)
if __name__=='__main__':
 try:
  if len(sys.argv)==3 and sys.argv[1]=='--payload-root':
   root=Path(sys.argv[2]);payload(root,load(root/'manifest.json'),['manifest.json']);print('fixture PASS')
  else:print(json.dumps(main(),indent=2))
 except Exception as e:print('FAIL: '+repr(e),file=sys.stderr);sys.exit(1)
