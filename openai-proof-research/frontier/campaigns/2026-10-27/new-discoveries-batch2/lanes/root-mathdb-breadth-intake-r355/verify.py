from pathlib import Path
import hashlib, json, sys, datetime
R=Path(__file__).resolve().parent
L=R.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s):
    assert p.stat().st_size==s and sha(p)==h,str(p)
def put(n,o): (R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
    check(Path(e['original']),e['sha256'],e['size'])
    check(R/e['copy'],e['sha256'],e['size'])
C=R/'frozen/sol-mathdb-primary-qualified-breadth-r352'
entries=json.loads((C/'manifest.json').read_text())['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in entries}
for e in entries: check(C/e['path'],e['sha256'],e['size'])
refs=json.loads((C/'input-bindings.json').read_text())
for e in refs: check(Path(e['path']),e['sha256'],e['size'])
inventory=L/'pi-mathdb-full-corpus-inventory-r301'
corpus=[e for e in json.loads((inventory/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(corpus)==20
for e in corpus: check(inventory/e['path'],e['sha256'],e['bytes'])
old=json.loads((R/'frozen/root-mathdb-breadth-intake-r350/coverage-delta.json').read_text())
d=json.loads((C/'dispositions.json').read_text())
rows=d['dispositions']; ids=[str(x['mathdb_id']) for x in rows]
reserved=json.loads((R/'frozen/root-mathdb-breadth-intake-r350/reserved-ids.json').read_text())['ids']
assert len(old)==483 and len(ids)==len(set(ids))==50 and set(ids)==set(map(str,reserved)) and not set(ids)&set(old)
records={str(x['mathdb_id']):x for x in json.loads((C/'records.json').read_text())}
assert set(records)==set(ids)
for x in rows:
    assert x['literal_statement']==records[str(x['mathdb_id'])]['statement']
    assert x['literal_statement_sha256']==hashlib.sha256(x['literal_statement'].encode()).hexdigest()
assert sum(x['primary_body_review'] for x in rows)==6
assert sum(x['full_resolution_proof_body_read'] for x in rows)==3
coverage=dict(old)
for x in rows:
    coverage[str(x['mathdb_id'])]={'disposition':x['disposition'],'record_statement_review':'delegate_reported_complete','report':'sol-mathdb-primary-qualified-breadth-r352/dispositions.json','primary_body_review_reported':x['primary_body_review'],'resolution_proof_body_read_reported':x['full_resolution_proof_body_read'],'source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0}
queue=[json.loads(s) for s in (R/'frozen/root-mathdb-breadth-intake-r326/frozen/pi-mathdb-full-corpus-inventory-r301/tags/review-queue-top.jsonl').read_text().splitlines()]
selected=[];seen=set(coverage)
for x in queue:
    n=str(x['mathdb_id'])
    if n in seen or x['status']!='open' or x['statement_completeness']!='full': continue
    selected.append(x);seen.add(n)
    if len(selected)==50: break
assert len(selected)==50
reservation={'ids':[x['mathdb_id'] for x in selected],'lane':'sol-mathdb-primary-qualified-breadth-r356','status':'reserved_not_reviewed'}
def payload(): return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
    put('coverage-delta.json',coverage);put('queue.json',selected);put('reserved-ids.json',reservation)
    put('manifest.json',{'files':[{'path':s,'sha256':sha(R/s),'size':(R/s).stat().st_size} for s in sorted(payload())]})
elif sys.argv[1]=='verify':
    assert json.loads((R/'coverage-delta.json').read_text())==coverage
    assert json.loads((R/'queue.json').read_text())==selected
    assert json.loads((R/'reserved-ids.json').read_text())==reservation
    own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
    for e in own: check(R/e['path'],e['sha256'],e['size'])
    put('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bindings),'child_payloads':len(entries),'live_input_bindings':len(refs),'corpus_chunks':20,'reported_statement_reviews':len(coverage),'reported_primary_screens':6,'reported_resolution_proof_bodies':3,'new_reservations':50,'root_payloads':len(own),'math_replay':False})
else: raise ValueError('build or verify')
print('PASS',sys.argv[1],len(coverage),'reported reviews',len(refs),'input hashes')
