from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent;L=R.parent;I=L/'root-mathdb-breadth-intake-r395';C=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def check(p,e):
 assert p.is_file(),str(p)
 size=e.get('size',e.get('bytes'))
 assert size is None or p.stat().st_size==size,'size: '+str(p)
 assert sha(p)==e['sha256'],'sha256: '+str(p)
def load(p):return json.loads(p.read_text())
refs=load(R/'input-bindings.json')['refs']
assert len({e['path'] for e in refs})==len(refs)
for e in refs:check(Path(e['path']),e)
assert not (R/'input-bindings.json').stat().st_mode&0o222
# Upstream checks are entirely read-only, including all originals, never their verifier.
root_entries=load(I/'manifest.json')['files']
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in root_entries}
for e in root_entries:check(I/e['path'],e)
for e in load(I/'bindings.json'):
 check(Path(e['original']),e);check(I/e['copy'],e)
for e in load(L/'root-mathdb-accepted-exclusions-r304/bindings.json'):check(Path(e['original']),e)
assert load(R/'historical-binding-mismatches.json')==[]
chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(C/e['path'],e)
reservation=load(I/'reserved-ids.json');assigned=reservation['ids'];active=reservation['other_active_reservations'];coverage=load(I/'coverage-delta.json')
a=set(map(str,assigned));b=set(map(str,active))
assert reservation['lane']==R.name and len(assigned)==len(a)==50 and len(active)==len(b)==50 and len(coverage)==1283
assert not a&b and not a&set(coverage) and not a&{'372627','372628','368940'}
assert a=={str(x['mathdb_id']) for x in load(I/'queue.json')}
found={}
for e in chunks:
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line);n=str(x['mathdb_id'])
   if n in a:
    assert n not in found;found[n]=x
assert set(found)==a
rows=load(R/'dispositions.json');records=load(R/'records.json')
assert len(rows)==50 and {str(x['mathdb_id']) for x in rows}==a
assert len(records)==50 and {str(x['mathdb_id']):x for x in records}==found
for x in rows:
 original=found[str(x['mathdb_id'])]
 assert x['literal_statement']==original['statement'] and x['url']==original['canonical_url'] and x['source_url']==original['source_url']
 assert hashlib.sha256(x['literal_statement'].encode()).hexdigest()==x['literal_sha256']
 assert hashlib.sha256(json.dumps(original,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()==x['canonical_record_sha256']
 assert x['literal_review'] and x['quantifiers_and_scope'] and x['reason'] and x['accepted_credit']==0 and not x['proposal']
 assert not x['selected_primary_body_read'] and not x['proof_section_read'] and not x['dependency_audit'] and not x['prior_cleared'] and not x['source_scope_cleared']
assert load(R/'proposals.json')==[] and load(R/'registry-status.json')['status']=='HOLD'
entries=load(R/'manifest.json')['files'];payload={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'}
assert payload=={e['path'] for e in entries} and len(entries)==len(payload)
for e in entries:check(R/e['path'],e)
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_original_refs_rehashed':len(refs),'root_manifest_payloads_verified_read_only':len(root_entries),'corpus_chunks_rehashed_in_place':20,'assigned_statement_and_canonical_record_hashes_verified':50,'reviewed_ids_disjoint':1283,'other_active_reservations_disjoint':50,'focused_ids_disjoint':[372627,372628,368940],'payload_files_verified':len(payload),'manifest_sha256':sha(R/'manifest.json'),'proposals':0,'primary_bodies_read':0,'proof_sections_read':0,'current_registry_clearance':'HOLD','accepted_credit':0,'upstream_writes':0,'scientific_exhaustiveness_claimed':False}
(R/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
