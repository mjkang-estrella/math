"""Read-only upstream verification; writes only this lane's final receipt on PASS."""
from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent;L=R.parent;I=L/'root-mathdb-breadth-intake-r387';C=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def check(p,e):
 assert p.is_file() and p.stat().st_size==e.get('size',e.get('bytes')) and sha(p)==e['sha256'],str(p)
def j(p):return json.loads(p.read_text())
def exact_manifest(root):
 entries=j(root/'manifest.json')['files']; names=[e['path'] for e in entries]
 assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
 assert set(names)==actual,(str(root),'payload mismatch',actual^set(names))
 for e in entries:check(root/e['path'],e)
 return len(entries)
payload_count=exact_manifest(R)
refs=j(R/'input-bindings.json');assert len(refs)==len({e['path'] for e in refs})
for e in refs:check(Path(e['path']),e)
intake_count=exact_manifest(I)
for e in j(I/'bindings.json'):
 check(Path(e['original']),e);check(I/e['copy'],e)
# Explicitly require, rather than merely incidentally include, critical original references.
required=[I/n for n in ['manifest.json','bindings.json','coverage-delta.json','queue.json','reserved-ids.json']]+[C/'manifest.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/disposition.json']
assert set(map(str,required)) <= {e['path'] for e in refs}
chunks=[e for e in j(C/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:check(C/e['path'],e)
r=j(I/'reserved-ids.json');assigned=list(map(int,r['ids']));others=set(map(int,r['other_active_reservations']));old=j(I/'coverage-delta.json')
assert r['lane']==R.name and len(assigned)==len(set(assigned))==50 and len(others)==50 and len(old)==1083
assert not set(assigned)&(others|set(map(int,old))|{372627,372628,368940})
assert set(assigned)=={int(x['mathdb_id']) for x in j(I/'queue.json')}
found={}
for e in chunks:
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line);n=int(x['mathdb_id'])
   if n in assigned:
    assert n not in found;found[n]=x
assert set(found)==set(assigned)
rows=j(R/'dispositions.json');assert len(rows)==50 and len({x['mathdb_id'] for x in rows})==50 and {x['mathdb_id'] for x in rows}==set(assigned)
assert j(R/'records.json')==[found[n] for n in assigned]
for x in rows:
 orig=found[x['mathdb_id']]
 assert x['statement']==orig['statement']==x['exact_scope']
 assert hashlib.sha256(x['statement'].encode()).hexdigest()==x['statement_sha256']
 assert hashlib.sha256(json.dumps(orig,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()==x['record_sha256_canonical_json']
 assert x['statement_review_complete'] is True and x['credit']==0 and x['proposal'] is False
 assert x['complete_dependency_audit'] is False and x['prior_cleared'] is False and x['source_scope_cleared'] is False
assert sum(x['primary_body_read'] for x in rows)==5 and sum(x['proof_section_read'] for x in rows)==2
assert j(R/'proposals.json')==[]
for name in ['source-provenance.json','additional-provenance.json']:
 for e in j(R/name):
  if 'path' in e:check(R/e['path'],e)
assert len(j(R/'failures.json'))==1 and j(R/'failures.json')[0]['kind']=='native_path_discovery'
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payload_files':payload_count,'intake_payload_files':intake_count,'actual_original_references_rehashed':len(refs),'original_corpus_chunks_rehashed':20,'reservation_exact':50,'reviewed_ids_disjoint':1083,'other_active_ids_disjoint':50,'literal_statement_hashes':50,'canonical_record_hashes':50,'statement_reviews':50,'selected_primary_reads':5,'selected_proof_section_reads':2,'complete_dependency_audits':0,'registry_clearances':0,'proposals':0,'credit_changes':0,'scientific_independent_review':False}
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
