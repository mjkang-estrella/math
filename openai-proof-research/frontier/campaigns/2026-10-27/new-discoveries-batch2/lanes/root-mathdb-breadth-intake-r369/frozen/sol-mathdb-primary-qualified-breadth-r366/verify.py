from pathlib import Path
import json,hashlib,datetime,sys
R=Path(__file__).resolve().parent;L=R.parent
def load(p):return json.loads(p.read_text())
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')) and hashlib.sha256(b).hexdigest()==e['sha256'],str(p)
refs=load(R/'input-bindings.json')
assert len({e['path'] for e in refs})==len(refs)
for e in refs:check(Path(e['path']),e)
I=L/'root-mathdb-breadth-intake-r365';C=L/'pi-mathdb-full-corpus-inventory-r301'
for e in load(I/'manifest.json')['files']:check(I/e['path'],e)
for e in load(I/'bindings.json'):check(Path(e['original']),e)
chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(C/e['path'],e)
a=load(I/'reserved-ids.json')['ids'];sets=[a]+[load(L/n/'reserved-ids.json')['ids'] for n in ['root-mathdb-gram-intake-r359','root-mathdb-cayley-review-intake-r363']]
assert all(len(s)==len(set(s))==50 for s in sets) and len(set(sum(sets,[])))==150
assert sets==load(R/'freeze-receipt.json')['sets']
assert set(a)=={x['mathdb_id'] for x in load(I/'queue.json')}
cov=load(I/'coverage-delta.json');assert len(cov)==633 and not set(map(str,a))&set(cov)
records=load(R/'records.json');assert len(records)==50 and {x['mathdb_id'] for x in records}==set(a)
found={}
for e in chunks:
 for line in (C/e['path']).read_text().splitlines():
  x=json.loads(line);n=int(x.get('mathdb_id',x.get('id',0)))
  if n in a:assert n not in found;found[n]=x
assert records==[found[n] for n in a]
rows=load(R/'dispositions.json')['dispositions'];assert len(rows)==50 and len({x['mathdb_id'] for x in rows})==50 and {x['mathdb_id'] for x in rows}==set(a)
for x in rows:
 assert x['literal_statement']==found[x['mathdb_id']]['statement']
 assert x['literal_statement_sha256']==hashlib.sha256(x['literal_statement'].encode()).hexdigest()
 assert x['record_statement_read'] and x['reason'] and x['accepted_credit']==0 and not x['eligible_proposal'] and not x['complete_dependency_audit']
assert sum(x['primary_body_review'] for x in rows)==5 and sum(x['concluding_resolution_proof_read'] for x in rows)==2
assert load(R/'proposals.json')==[]
for name in ['source-provenance.json','successor-provenance.json']:
 for e in load(R/name):
  if 'path' in e:check(R/e['path'],e)
for c in load(R/'bounded-checks.json')['checks']:assert c['printed_row_alternating_sum']==c['Catalan']
expected={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
entries=load(R/'manifest.json')['files'];assert len(entries)==len({e['path'] for e in entries}) and expected=={e['path'] for e in entries}
for e in entries:check(R/e['path'],e)
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),original_input_bindings=len(refs),corpus_chunks=20,reservation_sets=[50,50,50],pairwise_disjoint=True,baseline_coverage=633,individual_dispositions=50,primary_body_screens=5,concluding_successor_proofs_read=2,complete_dependency_audits=0,proposals=0,credit=0,manifest_payload_files=len(entries),manifest_sha256=hashlib.sha256((R/'manifest.json').read_bytes()).hexdigest(),counts_unchanged=True,mathematical_independent_review=False)
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
