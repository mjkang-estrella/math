from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent;L=R.parent
EX={'manifest.json','verification-receipt.json'}
def load(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,e):
 assert p.is_file(),str(p)
 assert sha(p)==e['sha256'],('hash',str(p))
 if 'size' in e or 'bytes' in e:assert p.stat().st_size==e.get('size',e.get('bytes')),('size',str(p))
def payload(p,ex):return {str(q.relative_to(p)) for q in p.rglob('*') if q.is_file()}-ex
own=load(R/'manifest.json')['files'];assert payload(R,EX)=={e['path'] for e in own}
assert len(own)==len({e['path'] for e in own})
for e in own:check(R/e['path'],e)
refs=load(R/'input-bindings.json');assert len(refs)==len({e['path'] for e in refs})
for e in refs:check(Path(e['path']),e)
I=L/'root-mathdb-breadth-intake-r369';entries=load(I/'manifest.json')['files']
assert payload(I,EX)=={e['path'] for e in entries}
for e in entries:check(I/e['path'],e)
for e in load(I/'bindings.json'):
 check(Path(e['original']),e);check(I/e['copy'],e)
C=L/'pi-mathdb-full-corpus-inventory-r301';inventory=load(C/'manifest.json')['files'];chunks=[e for e in inventory if e['path'].startswith('corpus/')]
assert len(chunks)==20
bound={e['path']:e for e in refs}
assert str(C/'manifest.json') in bound
for e in chunks:
 p=C/e['path'];check(p,e);assert str(p) in bound and bound[str(p)]['sha256']==e['sha256']
A=L/'root-mathdb-accepted-exclusions-r304'
for e in load(A/'manifest.json'):check(A/e['path'],e)
assert load(A/'accepted-exclusions.json')['accepted_family_count']==39
for n in ['accepted-exclusions.json','historical-dispositions.json']:assert str(A/n) in bound
J=L/'root-mathdb-cayley-review-intake-r363'
assert load(J/'disposition.json')['credit']==0
for n in ['disposition.json','DECISION.md','manifest.json']:assert str(J/n) in bound
reserved=load(I/'reserved-ids.json')['ids'];queue=load(I/'queue.json');cov=load(I/'coverage-delta.json')
sets=[set(map(str,reserved))]
for n in ['root-mathdb-gram-intake-r359','root-mathdb-breadth-intake-r367']:
 p=L/n/'reserved-ids.json';assert str(p) in bound
 a=load(p)['ids'];assert len(a)==len(set(a))==50;sets.append(set(map(str,a)))
assert len(cov)==733 and len(reserved)==len(set(reserved))==50
assert len(set.union(*sets))==150 and all(not s&set(cov) for s in sets)
assert sets[0]=={str(x['mathdb_id']) for x in queue}
rows=load(R/'dispositions.json')['dispositions'];ids=[str(x['mathdb_id']) for x in rows]
assert len(ids)==len(set(ids))==50 and set(ids)==sets[0]
found={}
for e in chunks:
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line);n=str(x['mathdb_id'])
   if n in sets[0]:assert n not in found;found[n]=x
assert set(found)==sets[0]
assert load(R/'records.json')==[found[str(n)] for n in reserved]
for d in rows:
 assert d['literal_statement']==found[str(d['mathdb_id'])]['statement']
 assert d['literal_sha256']==hashlib.sha256(d['literal_statement'].encode()).hexdigest()
 assert d['literal_review'] and d['individual_reason'] and d['evidence_level']
 assert d['accepted_credit']==0 and not d['prior_cleared'] and not d['source_scope_cleared'] and not d['full_dependencies_reviewed']
assert sum(d['primary_body_review'] for d in rows)==9
assert sum(d['concluding_resolution_proof_read'] for d in rows)==2
assert load(R/'proposals.json')==[]
for e in load(R/'source-provenance.json'):
 check(R/e['path'],e)
 assert e['requested_utc'] and e['received_utc'] and e['version']
 if e.get('usable'):assert e['status']==200 and not e['challenge']
assert load(R/'bounded-checks.json')['status']=='PASS'
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(R/'manifest.json'),'payload_files':len(own),'external_original_bindings':len(refs),'intake_payload_files':len(entries),'corpus_chunks_checked_in_place':20,'exact_literal_reviews':50,'baseline':733,'other_active_ids':100,'all_sets_disjoint':True,'primary_body_reviews':9,'concluding_proof_sections_read':2,'full_dependency_audits':0,'proposals':0,'credit':0,'counts_unchanged':'9 additional / 39 total / next 40','separate_final_run':True,'independent_math_replay':'only bounded published k=3 arithmetic in bounded-checks.json; no universal proof replay'}
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
