#!/usr/bin/env python3
"""Independent read-only verifier. Run through the fixed helper guard; never executes upstream code."""
from pathlib import Path
import json,hashlib,sys
D=Path(__file__).resolve().parent
EXCLUDED={'manifest.json','final-verification-receipt.json'}
def load(p):return json.loads(p.read_bytes())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size',str(p));assert digest(b)==e['sha256'],('hash',str(p))
def payload(root):
 m=load(root/'manifest.json');assert set(m['excluded_exact_paths'])==EXCLUDED
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names));assert not set(names)&EXCLUDED
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual-EXCLUDED==set(names),('payload set',actual-EXCLUDED-set(names),set(names)-actual)
 for e in m['files']:
  p=(root/e['path']).resolve();assert p.is_relative_to(root.resolve());check(p,e)
 return m
try:
 if len(sys.argv)>1:
  assert sys.argv[1]=='--payload-only';payload(Path(sys.argv[2]));print('PAYLOAD PASS');sys.exit(0)
 m=payload(D);L=D.parent;I=L/'root-mathdb-breadth-intake-r549';R=L/'pi-mathdb-full-corpus-inventory-r301'
 flat=load(D/'flat-bindings.json')
 for e in flat:check(Path(e['path']),e)
 # Intake exact payload, every direct original/copy pair. No recursive expansion.
 im=load(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 pairs=load(I/'bindings.json')
 for e in pairs:
  check(Path(e['original']),e);check(Path(e['copy']),e);assert Path(e['original']).read_bytes()==Path(e['copy']).read_bytes()
 assert any(e['original']==str(R/'manifest.json') for e in pairs)
 inv=load(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/') and e['path'].endswith('.jsonl')];assert len(chunks)==20;assert len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check(R/e['path'],e)
 cov=load(I/'coverage-delta.json');assert len(cov)==4683
 reserved=load(I/'reserved-ids.json');ids=set(reserved['ids']);assert len(ids)==50 and reserved['lane']==D.name
 assert ids=={e['mathdb_id'] for e in load(I/'queue.json')}
 sets=[set(e['ids']) for e in load(I/'active-breadth-reservations.json')];assert len(sets)==3 and ids in sets
 for n,s in enumerate(sets):
  assert len(s)==50;assert not s&set(map(int,cov));assert not s&set(reserved['protected_ids'])
  for t in sets[:n]:assert not s&t
 assert set(reserved['other_active_reservations'])==set.union(*(s for s in sets if s!=ids))
 found={}
 for e in chunks:
  for n,line in enumerate((R/e['path']).open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(e['path'],n,r)
 ds=load(D/'dispositions.json');assert len(ds)==50 and {x['mathdb_id'] for x in ds}==ids and len(found)==50
 ar=load(D/'assigned-records.json');assert len(ar)==50
 for a in ar:assert (a['chunk'],a['line'],a['record'])==found[a['record']['mathdb_id']]
 for x in ds:
  chunk,n,r=found[x['mathdb_id']];assert x['corpus_chunk']==chunk and x['corpus_line']==n and x['statement']==r['statement']
  assert x['statement_utf8_sha256']==digest(r['statement'].encode('utf-8'))
  assert x['canonical_record_sha256']==digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  assert x['literal_full_statement_read'] and x['accepted_credit']==0
 assert len(load(D/'proposals.json'))<=3
 for name in ['retrieval-bindings.json','pdf-bindings.json','derivative-bindings.json']:
  for e in load(D/name):
   if 'error' not in e:check(D/e['path'],e)
 print(json.dumps(dict(status='INTEGRITY_PASS_ONLY',literal_reviews=50,baseline=4683,corpus_chunks=20,frozen_inputs=8,original_copy_pairs=len(pairs),proposals=len(load(D/'proposals.json')),manifest_sha256=digest((D/'manifest.json').read_bytes()),manifest_size=(D/'manifest.json').stat().st_size)))
except Exception as e:
 print('FAIL: '+repr(e),file=sys.stderr);sys.exit(1)
