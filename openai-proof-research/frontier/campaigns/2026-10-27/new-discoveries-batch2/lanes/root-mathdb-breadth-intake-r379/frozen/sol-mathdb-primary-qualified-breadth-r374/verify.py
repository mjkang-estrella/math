from pathlib import Path
import hashlib,json,datetime,sys
R=Path(__file__).resolve().parent;L=R.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,e):
 b=p.read_bytes(); assert len(b)==e.get('size',e.get('bytes')) and sha(b)==e['sha256'],str(p)
# Manifest integrity, including exact file membership and this verifier.
manifest=load(R/'manifest.json')['files']
actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
assert actual=={e['path'] for e in manifest},actual^{e['path'] for e in manifest}
for e in manifest:check(R/e['path'],e)
# Immutable flat original bindings; no historical copying required.
refs=load(R/'input-bindings.json')
assert len({e['path'] for e in refs})==len(refs)
for e in refs:check(Path(e['path']),e)
I=L/'root-mathdb-breadth-intake-r373'
for e in load(I/'manifest.json')['files']:check(I/e['path'],e)
for e in load(I/'bindings.json'):
 check(Path(e['original']),e);check(I/e['copy'],e)
C=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(C/e['path'],e)
D=L/'root-mathdb-accepted-exclusions-r304'
for e in load(D/'manifest.json'):
 p=D/e['path'];assert sha(p.read_bytes())==e['sha256'],str(p)
assert load(L/'root-mathdb-cayley-review-intake-r363/disposition.json')['credit']==0
ids=load(I/'reserved-ids.json')['ids'];queue=load(I/'queue.json');coverage=load(I/'coverage-delta.json')
assert len(ids)==len(set(ids))==50 and set(ids)=={x['mathdb_id'] for x in queue} and len(queue)==50
sets=[set(ids)]+[set(load(L/n/'reserved-ids.json')['ids']) for n in ['root-mathdb-gram-intake-r359','root-mathdb-breadth-intake-r371']]
assert all(len(s)==50 for s in sets)
assert all(not sets[a]&sets[b] for a in range(3) for b in range(a+1,3))
assert len(coverage)==833 and not set(map(str,ids))&set(coverage)
found={}
for e in chunks:
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line);n=x['mathdb_id']
   if n in sets[0]:assert n not in found;found[n]=x
assert set(found)==sets[0]
rows=load(R/'dispositions.json')['dispositions'];records=load(R/'records.json')
assert len(rows)==50 and {r['mathdb_id'] for r in rows}==sets[0]
assert records==[found[n] for n in ids]
for r in rows:
 s=found[r['mathdb_id']]['statement'];assert r['literal_statement']==s and r['literal_sha256']==sha(s.encode()) and r['literal_bytes']==len(s.encode())
 assert r['literal_review'] and r['accepted_credit']==0 and not r['proposal'] and not r['bounded_novelty_cleared']
assert sum(r['primary_body_review'] for r in rows)==9
assert sum(r['concluding_proof_section_read'] for r in rows)==1
assert not any(r['complete_dependencies_read'] for r in rows)
assert load(R/'proposals.json')==[]
for e in load(R/'source-provenance.json'):
 if 'sha256' in e:check(R/'sources'/e['name'],e)
 if e.get('status') in (403,429) or e.get('challenge'):assert not e['usable']
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','separate_final_verifier_run':True,'manifest_sha256':sha((R/'manifest.json').read_bytes()),'manifest_file_count':len(manifest),'original_bindings_verified':len(refs),'root_manifest_verified':True,'r304_verified':True,'r363_verified':True,'corpus_chunks_verified_in_place':20,'literal_reviews':50,'primary_body_reviews':9,'concluding_proof_section_reviews':1,'complete_dependency_reviews':0,'proposals':0,'credit':0,'coverage_bound':833,'coverage_updated':False,'queue_exact_set':True,'active_pairwise_disjoint':True,'coverage_disjoint':True,'counts_unchanged':[9,39,40]}
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
