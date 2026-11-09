from pathlib import Path
import hashlib,json,sys,datetime,collections
R=Path(__file__).resolve().parent;L=R.parent;T=L/'root-mathdb-breadth-intake-r383';I=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s):
 if p.stat().st_size!=s or sha(p)!=h:raise ValueError('hash/size mismatch: '+str(p))
def payload(r):return {str(p.relative_to(r)) for p in r.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
refs=json.loads((R/'input-bindings.json').read_text())
for e in refs:check(Path(e['path']),e['sha256'],e['size'])
entries=json.loads((T/'manifest.json').read_text())['files']
assert payload(T)=={e['path'] for e in entries},'root payload set'
for e in entries:check(T/e['path'],e['sha256'],e['size'])
for e in json.loads((T/'bindings.json').read_text()):
 check(Path(e['original']),e['sha256'],e['size']);check(T/e['copy'],e['sha256'],e['size'])
chunks=[e for e in json.loads((I/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:check(I/e['path'],e['sha256'],e['bytes'])
ids=json.loads((T/'reserved-ids.json').read_text())['ids'];cov=json.loads((T/'coverage-delta.json').read_text())
ds=json.loads((R/'dispositions.json').read_text());rs=json.loads((R/'records.json').read_text())
assert len(ds)==len(ids)==len(set(ids))==50 and len(cov)==1033
assert len({x['mathdb_id'] for x in ds})==50 and {x['mathdb_id'] for x in ds}==set(ids)=={x['mathdb_id'] for x in rs}
assert not set(map(str,ids))&set(cov) and not set(ids)&{372627,372628,368940}
assert {x['mathdb_id'] for x in json.loads((T/'queue.json').read_text())}==set(ids)
found={}
for e in chunks:
 with (I/e['path']).open() as f:
  for line in f:
   x=json.loads(line);n=x['mathdb_id']
   if n in ids:assert n not in found;found[n]=x
assert set(found)==set(ids)
for x in ds:
 original=found[x['mathdb_id']]
 assert x['statement']==original['statement']
 assert hashlib.sha256(x['statement'].encode()).hexdigest()==x['statement_sha256']
 assert hashlib.sha256(json.dumps(original,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()==x['record_sha256_canonical_json']
 assert x['credit']==0 and x['proposal'] is False and not x['complete_dependency_audit'] and x['novelty_clearance']=='HOLD'
 for e in x['primary_evidence']:assert sha(R/e['path'])==e['sha256']
assert {x['mathdb_id']:x for x in rs}==found
assert json.loads((R/'proposals.json').read_text())==[]
for e in json.loads((R/'source-provenance.json').read_text())+[json.loads((R/'published-provenance.json').read_text())]:
 if e['status']=='retained':check(R/'sources'/f"{e['key']}.pdf",e['sha256'],e['bytes'])
own=json.loads((R/'manifest.json').read_text())['files'];assert payload(R)=={e['path'] for e in own},'exact payload set'
for e in own:check(R/e['path'],e['sha256'],e['size'])
assert sum(x['primary_body_read'] for x in ds)==17 and sum(x['proof_section_read'] for x in ds)==3
if '--negative-control' in sys.argv:
 check(R/'dispositions.json','0'*64,(R/'dispositions.json').stat().st_size)
 raise AssertionError('negative control did not reject')
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_original_references':len(refs),'root_manifest_read_only_verified':True,'root_verifier_executed':False,'all_corpus_chunks_in_place':20,'literal_statements':50,'reported_prior_coverage':1033,'exact_reservation_equality':True,'disjoint':True,'focused_disjoint':True,'exact_payload_files':len(own),'manifest_sha256':sha(R/'manifest.json'),'evidence_counts':dict(collections.Counter(x['evidence_level'] for x in ds)),'proof_sections_read':3,'complete_dependency_audits':0,'novelty_clearances':0,'credit':0,'accepted_additional':9,'accepted_total':39,'next':40}
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
