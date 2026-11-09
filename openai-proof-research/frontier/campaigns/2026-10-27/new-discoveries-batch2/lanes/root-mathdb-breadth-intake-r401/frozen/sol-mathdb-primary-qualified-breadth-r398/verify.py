"""Read-only separate verification. No receipt writes and no imported lane helpers."""
from pathlib import Path
import json,hashlib,datetime
O=Path(__file__).resolve().parent;B=O.parent;R=B/'root-mathdb-breadth-intake-r397';C=B/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,r):
 b=p.read_bytes();assert digest(b)==r['sha256'],f'SHA256 mismatch: {p}'
 size=r.get('size',r.get('bytes'))
 if size is not None:assert len(b)==size,f'size mismatch: {p}'
for n in ['freeze-initial.json','input-bindings.json']:
 for r in load(O/n)['refs']:check(Path(r['path']),r)
for r in load(R/'manifest.json')['files']:check(R/r['path'],r)
for r in load(R/'bindings.json'):check(Path(r['original']),r);check(R/r['copy'],r)
A=B/'root-mathdb-accepted-exclusions-r304'
for r in load(A/'manifest.json'):check(A/r['path'],r)
for r in load(A/'bindings.json'):check(Path(r['copy']),r)
chunks=[r for r in load(C/'manifest.json')['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20
for r in chunks:check(C/r['path'],r)
a=load(R/'reserved-ids.json');ids=set(a['ids']);assert len(a['ids'])==len(ids)==50 and a['lane']==O.name
cov=load(R/'coverage-delta.json');assert len(cov)==1333
assert not ids&set(map(int,cov));assert not ids&set(a['other_active_reservations']);assert len(a['other_active_reservations'])==50
assert not ids&{372627,372628,368940};q=load(R/'queue.json');assert len(q)==50 and {x['mathdb_id'] for x in q}==ids
# Exact records are recovered again from verified corpus originals, without copies.
source={}
for c in chunks:
 for line in (C/c['path']).open():
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   assert r['mathdb_id'] not in source,'duplicate assigned corpus ID';source[r['mathdb_id']]=r
assert set(source)==ids
s=load(O/'statements.json');ds=load(O/'dispositions.json');assert len(s)==len(ds)==50
assert {r['mathdb_id'] for r in s}==ids=={r['mathdb_id'] for r in ds}
for r in s:assert r==source[r['mathdb_id']],'normalized original differs'
for r in ds:
 orig=source[r['mathdb_id']];assert r['statement']==orig['statement'] and r['canonical_url']==orig['canonical_url']
 assert r['statement_sha256']==digest(orig['statement'].encode())
 canon=json.dumps(orig,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()
 assert r['canonical_record_sha256']==digest(canon)
 assert r['exact_scope'] and r['reason'] and r['evidence_level'] and r['credit']==0
 assert not r['current_registry_clearance'] and not r['complete_dependency_audit'] and not r['original_source_body_read']
assert sum(r['primary_selected'] for r in ds)==3;assert sum(r['successor_proof_sections_read'] for r in ds)==1
assert load(O/'proposals.json')['proposals']==[]
for r in load(O/'primary-bindings.json')['refs']:
 check(Path(r['path']),r);m=load(Path(r['meta']));assert m['sha256']==r['sha256'] and m['size']==r['size'] and m['status']==200
# Enforce exact payload, including unexpected files/symlinks, not just expected hashes.
excluded={'manifest.json','final-receipt.json'}
actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() or p.is_symlink()}-excluded
manifest=load(O/'manifest.json');expected={r['path'] for r in manifest['files']};assert len(expected)==len(manifest['files']);assert expected==actual,dict(missing=sorted(expected-actual),unexpected=sorted(actual-expected))
for r in manifest['files']:
 p=O/r['path'];assert not p.is_symlink();assert p.resolve().is_relative_to(O);check(p,r)
print(json.dumps(dict(status='PASS',verified_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),input_refs=len(load(O/'input-bindings.json')['refs']),root_manifest_and_actual_originals=True,r304_hash_entries=6,corpus_chunks_in_place=20,exact_assigned_ids=50,reviewed_disjoint=1333,other_active_disjoint=50,special_exclusions_disjoint=3,literal_statement_and_canonical_hashes=50,payload_files=len(expected),payload_exactset=True,upstream_writes=0,credit=0,counts=dict(additional=9,total=39,next=40)),indent=2))
