from pathlib import Path
import json,hashlib,sys,datetime
R=Path(__file__).resolve().parent;L=R.parent;I=L/'root-mathdb-breadth-intake-r417'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,e):
 assert p.is_file(),str(p)
 assert p.stat().st_size==e.get('size',e.get('bytes')),('size',str(p))
 assert sha(p)==e['sha256'],('hash',str(p))
def payload():return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'}
# All checks read originals independently; no imports/execution of upstream verifiers.
bind=read(R/'bindings.json')['references']
for e in bind:check(Path(e['path']),e)
root=read(I/'manifest.json')['files']
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in root}
for e in root:check(I/e['path'],e)
C=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in read(C/'manifest.json')['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(C/e['path'],e)
reservation=read(I/'reserved-ids.json');ids=set(map(str,reservation['ids']));other=set(map(str,reservation['other_active_reservations']));old=set(read(I/'coverage-delta.json'))
assert len(ids)==50 and len(other)==50 and len(old)==1833
assert not ids&(other|old|{'372627','372628','368940'})
assert ids=={str(x['mathdb_id']) for x in read(I/'queue.json')}
assert reservation['lane']==R.name
rows=read(R/'dispositions.json');assert len(rows)==50 and {str(x['mathdb_id']) for x in rows}==ids
found={}
for e in chunks:
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line);n=str(x['mathdb_id'])
   if n in ids:
    assert n not in found;found[n]=x
assert set(found)==ids
assert {str(x['mathdb_id']):x for x in read(R/'selected-records.json')}==found
for x in rows:
 y=found[str(x['mathdb_id'])]
 assert x['literal_statement']==y['statement']==x['scope']
 assert x['statement_sha256']==hashlib.sha256(y['statement'].encode()).hexdigest()
 assert x['canonical_record_sha256']==hashlib.sha256(json.dumps(y,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
 assert x['credit']==0 and x['reason'] and x['original_body_read']
 assert x['dedup_prior']['current_registry'].startswith('HOLD')
evs=read(R/'evidence.json');assert len(evs)==50 and {e['mathdb_id'] for e in evs}=={x['mathdb_id'] for x in rows}
for x in rows:
 e=evs[x['primary_evidence_index']];assert e['mathdb_id']==x['mathdb_id']
for e in evs:
 a,b=e['lines'];excerpt='\n'.join((R/e['source_text']).read_text().split('\n')[a-1:b])
 assert e['excerpt']==excerpt
 assert e['excerpt_sha256']==hashlib.sha256(excerpt.encode()).hexdigest()
 assert e['pdf_sha256']==sha(R/e['pdf'])
for name in ['provenance.json','successor-bodies-provenance.json','successor-provenance.json']:
 for e in read(R/name):
  if e.get('path'):check(Path(e['path']),e)
assert read(R/'proposals.json')==[]
if sys.argv[1:] == ['seal']:
 (R/'manifest.json').write_text(json.dumps({'exclusions':['manifest.json','final-receipt.json'],'files':[{'path':p,'sha256':sha(R/p),'size':(R/p).stat().st_size} for p in sorted(payload())]},indent=2)+'\n')
else:assert sys.argv[1:]==['verify']
m=read(R/'manifest.json');assert set(m['exclusions'])=={'manifest.json','final-receipt.json'}
assert payload()=={e['path'] for e in m['files']}
assert len(m['files'])==len({e['path'] for e in m['files']})
for e in m['files']:check(R/e['path'],e)
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_references_checked':len(bind),'root_payloads_checked_read_only':len(root),'original_corpus_chunks_checked_in_place':20,'literal_and_canonical_hashes_checked':50,'exact_assignment_and_disjointness':True,'reviewed_exclusion_count':1833,'other_reserved_count':50,'payload_count':len(m['files']),'manifest_sha256':sha(R/'manifest.json'),'qualified_proposals':0,'credit':0,'counts':'9 additional /39 total /next40 unchanged','upstream_receipt_writer_executed':False,'mathematical_independent_acceptance_review':False}
(R/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
