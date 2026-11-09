from pathlib import Path
import json,hashlib,datetime,sys
R=Path(__file__).resolve().parent;L=R.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s):
 assert p.stat().st_size==s and sha(p)==h,str(p)
def payload(d,excluded):return {str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-excluded
refs=json.loads((R/'bindings.json').read_text())['references']
assert len({e['path'] for e in refs})==len(refs)
for e in refs:check(Path(e['path']),e['sha256'],e['size'])
I=L/'root-mathdb-breadth-intake-r411'
root=json.loads((I/'manifest.json').read_text())['files']
assert payload(I,{'manifest.json','verification-receipt.json'})=={e['path'] for e in root}
for e in root:check(I/e['path'],e['sha256'],e['size'])
for e in json.loads((I/'bindings.json').read_text()):check(Path(e['original']),e['sha256'],e['size'])
C=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in json.loads((C/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(C/e['path'],e['sha256'],e['bytes'])
res=json.loads((I/'reserved-ids.json').read_text());ids=set(map(str,res['ids']))
assert res['lane']==R.name
old=json.loads((I/'coverage-delta.json').read_text())
assert len(ids)==50 and len(old)==1683 and not ids&set(old)
assert not ids&set(map(str,res['other_active_reservations'])) and not ids&{'372627','372628','368940'}
rows=json.loads((R/'dispositions.json').read_text());assert len(rows)==50 and {str(x['mathdb_id']) for x in rows}==ids
originals={}
for e in chunks:
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line);n=str(x['mathdb_id'])
   if n in ids:
    assert n not in originals;originals[n]=x
assert set(originals)==ids
for x in rows:
 original=originals[str(x['mathdb_id'])]
 assert x['literal_statement']==original['statement']==x['full_scope_and_quantifiers']
 assert hashlib.sha256(original['statement'].encode()).hexdigest()==x['statement_sha256']
 assert hashlib.sha256(json.dumps(original,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()==x['canonical_record_sha256']
 assert x['reason'] and x['scope_note'] and x['evidence_level'] and x['accepted_credit']==0
 assert not x['source_scope_cleared'] and x['current_registry_clearance'].startswith('HOLD')
assert json.loads((R/'records.json').read_text())==[originals[str(x['mathdb_id'])] for x in rows]
assert json.loads((R/'proposals.json').read_text())==[]
for p in (R/'evidence').glob('*.provenance.json'):
 m=json.loads(p.read_text())
 if 'path' in m:check(R/m['path'],m['sha256'],m['size'])
# The only own-payload exclusions are these exact relative paths.
files=json.loads((R/'manifest.json').read_text())['files']
assert payload(R,{'manifest.json','finalreceipt.json'})=={e['path'] for e in files}
assert len({e['path'] for e in files})==len(files)
for e in files:check(R/e['path'],e['sha256'],e['size'])
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'frozen_original_refs':len(refs),'root_manifest_read_only':True,'root_receipt_writer_executed':False,'corpus_chunks_verified_in_place':20,'literal_and_canonical_record_hashes_checked':50,'exact_reserved_set':50,'reviewed_disjoint':1683,'other_reserved_disjoint':True,'special_exclusions_disjoint':True,'manifest_payloads':len(files),'proposal_count':0,'credit':0,'counts':{'additional':9,'total':39,'next':40},'mathematical_acceptance':False}
(R/'finalreceipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
