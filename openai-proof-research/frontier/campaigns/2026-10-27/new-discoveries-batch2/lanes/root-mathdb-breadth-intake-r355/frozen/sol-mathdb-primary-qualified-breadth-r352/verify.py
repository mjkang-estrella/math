#!/usr/bin/env python3
"""Read-only verification except for the explicitly excluded receipt; any mismatch exits nonzero."""
from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent;B=L.parent
EXCLUDED={'manifest.json','verification-receipt.json'}
def check(p,h,size=None):
 b=p.read_bytes()
 if size is not None and len(b)!=size:raise ValueError(f'size mismatch: {p}')
 if hashlib.sha256(b).hexdigest()!=h:raise ValueError(f'SHA256 mismatch: {p}')
 return len(b)
def manifest(p,corpus_only=False):
 m=json.loads((p/'manifest.json').read_text());entries=m['files'] if isinstance(m,dict) else m
 n=0
 for r in entries:
  if corpus_only and not r['path'].startswith('corpus/'):continue
  check(p/r['path'],r['sha256'],r.get('size',r.get('bytes')));n+=1
 return n
bindings=json.loads((L/'input-bindings.json').read_text())
for r in bindings:check(Path(r['path']),r['sha256'],r['size'])
assert manifest(B/'root-mathdb-breadth-intake-r350')==25
assert manifest(B/'pi-mathdb-full-corpus-inventory-r301',True)==20
manifest(B/'root-mathdb-accepted-exclusions-r304')
root=B/'root-mathdb-breadth-intake-r350'
for r in json.loads((root/'bindings.json').read_text()):
 check(Path(r['original']),r['sha256'],r['size']);check(root/r['copy'],r['sha256'],r['size'])
ids=json.loads((root/'reserved-ids.json').read_text())['ids'];assert len(ids)==len(set(ids))==50
queue=json.loads((root/'queue.json').read_text());assert [r['mathdb_id'] for r in queue]==ids
cov=json.loads((root/'coverage-delta.json').read_text());assert len(cov)==483;assert not set(ids)&set(map(int,cov))
found={}
for p in sorted((B/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for line in p.open():
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   assert r['mathdb_id'] not in found;found[r['mathdb_id']]=r
records=json.loads((L/'records.json').read_text());assert records==[found[i] for i in ids]
for q in queue:
 assert q['title']==found[q['mathdb_id']]['title']
old=B/'pi-mathdb-primary-qualified-breadth-r351'
assert {r['mathdb_id']:r for r in json.loads((old/'work/records.json').read_text())}==found
old_bound={Path(r['path']) for r in bindings if str(old)+'/' in r['path']}
assert old_bound=={p for p in old.rglob('*') if p.is_file()}
d=json.loads((L/'dispositions.json').read_text());rows=d['dispositions']
assert [r['mathdb_id'] for r in rows]==ids
assert len(rows)==d['reviewed_count']==50 and d['new_result_count']==0 and d['promising_briefs']==[]
assert sum(r['primary_body_review'] for r in rows)==6
assert sum(r['full_resolution_proof_body_read'] for r in rows)==3
for r in rows:
 assert r['literal_statement']==found[r['mathdb_id']]['statement']
 assert r['literal_statement_sha256']==hashlib.sha256(r['literal_statement'].encode()).hexdigest()
 assert r['accepted_credit']==0 and r['prior_art_cleared'] is False and r['formal_evidence']=='none'
 assert r['reason'] and r['disposition']
for r in json.loads((L/'source-provenance.json').read_text()):
 assert r['status']==200;check(L/r['file'],r['sha256'],r['size'])
m=json.loads((L/'manifest.json').read_text())['files'];listed={r['path'] for r in m}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in EXCLUDED}
assert listed==actual,{'missing_from_manifest':sorted(actual-listed),'missing_files':sorted(listed-actual)}
for r in m:check(L/r['path'],r['sha256'],r['size'])
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_originals_checked':len(bindings),'r350_manifest_files':25,'r301_chunks':20,'reserved_ids':50,'dispositions':50,'primary_body_screens':6,'published_resolution_proof_bodies':3,'r350_overlap':0,'r351_partial_extract_overlap':50,'accepted_credit':0,'manifest_files':len(m),'manifest_sha256':hashlib.sha256((L/'manifest.json').read_bytes()).hexdigest(),'excluded_only':sorted(EXCLUDED)}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
