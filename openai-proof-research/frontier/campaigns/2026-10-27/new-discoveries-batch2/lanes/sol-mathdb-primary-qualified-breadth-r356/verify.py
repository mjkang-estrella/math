from pathlib import Path
import hashlib,json,datetime,sys,math
L=Path(__file__).resolve().parent;B=L.parent
EXCLUDED={'manifest.json','verification-receipt.json'}
def load(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,e):
 assert p.is_file(),f'missing {p}'
 assert sha(p)==e['sha256'],f'hash {p}'
 size=e.get('size',e.get('bytes'))
 if size is not None:assert p.stat().st_size==size,f'size {p}'
def payload():return {str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-EXCLUDED
# Negative modes must actually exit nonzero on set/hash corruption, without touching evidence.
if '--test-bad-hash' in sys.argv:
 check(L/'records.json',{'sha256':'0'*64});raise RuntimeError('undetected bad hash')
if '--test-bad-set' in sys.argv:
 assert payload()==set(), 'deliberate payload set mismatch';raise RuntimeError('undetected bad set')
refs=load(L/'input-bindings.json')+load(L/'supplementary-bindings.json')
assert len({e['path'] for e in refs})==len(refs)
for e in refs:check(Path(e['path']),e)
root=B/'root-mathdb-breadth-intake-r355';rootentries=load(root/'manifest.json')['files']
actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-EXCLUDED
assert actual=={e['path'] for e in rootentries}
for e in rootentries:check(root/e['path'],e)
for e in load(root/'bindings.json'):check(Path(e['original']),e)
inv=B/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in load(inv/'manifest.json')['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
assert {str(p.relative_to(inv)) for p in (inv/'corpus').glob('*.jsonl')}=={e['path'] for e in chunks}
for e in chunks:check(inv/e['path'],e)
ids=list(map(str,load(root/'reserved-ids.json')['ids']));queue=load(root/'queue.json');coverage=load(root/'coverage-delta.json')
assert len(ids)==len(set(ids))==50 and set(ids)=={str(x['mathdb_id']) for x in queue}
assert len(coverage)==533 and not set(ids)&set(coverage) and not set(ids)&{'364119','404067'}
def associations(x):
 out=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if k=='mathdb_id':out.add(str(v))
   elif k in ('mathdb_ids','problem_ids'):out.update(map(str,v))
   else:out|=associations(v)
 elif isinstance(x,list):
  for v in x:out|=associations(v)
 return out
ex=B/'root-mathdb-accepted-exclusions-r304'
assert not set(ids)&associations(load(ex/'accepted-exclusions.json'))
assert not set(ids)&associations(load(ex/'historical-dispositions.json'))
rows=load(L/'dispositions.json')['dispositions'];records=load(L/'records.json')
assert len(rows)==len(records)==50 and {str(x['mathdb_id']) for x in rows}==set(ids)
assert len({x['mathdb_id'] for x in rows})==50
originals={}
for e in chunks:
 with (inv/e['path']).open() as f:
  for ln,line in enumerate(f,1):
   r=json.loads(line);n=str(r['mathdb_id'])
   if n in ids:
    assert n not in originals
    originals[n]=(r,str(inv/e['path']),ln)
assert set(originals)==set(ids)
for r in records:
 o,path,ln=originals[str(r['mathdb_id'])]
 assert r['statement']==o['statement'] and r['corpus_path']==path and r['corpus_line']==ln
for r in rows:
 o,path,ln=originals[str(r['mathdb_id'])]
 assert r['literal_statement']==o['statement']
 assert r['literal_statement_sha256']==hashlib.sha256(o['statement'].encode()).hexdigest()
 assert r['reason'] and r['accepted_credit']==0 and r['record_statement_review']
assert sum(r['primary_body_review'] for r in rows)==3
assert sum(r['resolution_proof_body_section_read'] for r in rows)==2
assert sum(r['full_resolution_proof_body_read'] for r in rows)==0
assert load(L/'proposals.json')==[]
for e in load(L/'source-provenance.json'):assert e['status']==200;check(L/e['path'],e)
q=[1,1]
for i in range(2,13):q.append(2*q[-1]+q[-2])
c=load(L/'bounded-checks.json');assert c['Q_0_through_Q_12']==q
assert q[12]==19601 and math.gcd(q[12],12)==1 and q[2]%3==0 and q[1]%3!=0 and 12%3==12%2==0
own=load(L/'manifest.json')['files'];assert len(own)==len({e['path'] for e in own})
assert payload()=={e['path'] for e in own}
for e in own:check(L/e['path'],e)
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_original_refs_rechecked':len(refs),'root_payloads_rechecked':len(rootentries),'all_corpus_chunks_rechecked_in_place':20,'exact_reservation_set':50,'new_statement_reviews':50,'prior_reported':533,'potential_union_subject_to_root':583,'primary_body_reviews':3,'resolution_proof_sections':2,'full_resolution_dependency_audits':0,'proposals':0,'discovery_credit':0,'counts':{'additional':9,'total':39,'next':40},'payload_count':len(own),'manifest_sha256':sha(L/'manifest.json')}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
