from pathlib import Path
import hashlib,json,sys,datetime
R=Path(__file__).resolve().parent;L=R.parent
C=R/'frozen/sol-mathdb-primary-qualified-breadth-r364'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s): assert p.stat().st_size==s and sha(p)==h,str(p)
def put(n,o): (R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
    check(Path(e['original']),e['sha256'],e['size']);check(R/e['copy'],e['sha256'],e['size'])
entries=json.loads((C/'manifest.json').read_text())['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in entries}
for e in entries: check(C/e['path'],e['sha256'],e['size'])
refs=json.loads((C/'bindings.json').read_text())['files']
for e in refs: check(Path(e['path']),e['sha256'],e['size'])
I=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in json.loads((I/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks: check(I/e['path'],e['sha256'],e['bytes'])
old=json.loads((R/'frozen/root-mathdb-breadth-intake-r365/coverage-delta.json').read_text())
reserved=json.loads((R/'frozen/root-mathdb-cayley-review-intake-r363/reserved-ids.json').read_text())['ids']
rows=json.loads((C/'dispositions.json').read_text());ids=[str(x['mathdb_id']) for x in rows]
assert len(old)==633 and len(ids)==len(set(ids))==50 and set(ids)==set(map(str,reserved)) and not set(ids)&set(old)
found={}
for e in chunks:
    with (I/e['path']).open() as f:
        for line in f:
            x=json.loads(line);n=str(x['mathdb_id'])
            if n in ids:
                assert n not in found;found[n]=x
assert set(found)==set(ids)
for x in rows: assert x['literal_statement']==found[str(x['mathdb_id'])]['statement'] and x['credit']==0
assert sum(x['primary_statement_review'] for x in rows)==5
coverage=dict(old)
for x in rows:
    coverage[str(x['mathdb_id'])]={'disposition':x['disposition'],'record_statement_review':'delegate_reported_complete','report':'sol-mathdb-primary-qualified-breadth-r364/dispositions.json','primary_body_review_reported':x['primary_statement_review'],'concluding_proof_section_reported':x['concluding_proof_section_review'],'proof_dependency_scope_reported':x['complete_proof_coverage_scope'],'source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0}
held=[]
for n in ['root-mathdb-gram-intake-r359','root-mathdb-breadth-intake-r365']:
    held+=json.loads((R/'frozen'/n/'reserved-ids.json').read_text())['ids']
assert len(held)==len(set(held))==100 and not set(map(str,held))&set(coverage)
queue=[json.loads(s) for s in (R/'frozen/root-mathdb-breadth-intake-r326/frozen/pi-mathdb-full-corpus-inventory-r301/tags/review-queue-top.jsonl').read_text().splitlines()]
selected=[];seen=set(coverage)|set(map(str,held))
for x in queue:
    n=str(x['mathdb_id'])
    if n in seen or x['status']!='open' or x['statement_completeness']!='full':continue
    selected.append(x);seen.add(n)
    if len(selected)==50:break
assert len(selected)==50
reservation={'ids':[x['mathdb_id'] for x in selected],'lane':'sol-mathdb-primary-qualified-breadth-r368','status':'reserved_not_reviewed','other_active_reservations':['root-mathdb-gram-intake-r359/reserved-ids.json','root-mathdb-breadth-intake-r365/reserved-ids.json']}
def payload():return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
    put('coverage-delta.json',coverage);put('queue.json',selected);put('reserved-ids.json',reservation)
    put('manifest.json',{'files':[{'path':s,'sha256':sha(R/s),'size':(R/s).stat().st_size} for s in sorted(payload())]})
elif sys.argv[1]=='verify':
    assert json.loads((R/'coverage-delta.json').read_text())==coverage
    assert json.loads((R/'queue.json').read_text())==selected and json.loads((R/'reserved-ids.json').read_text())==reservation
    own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
    for e in own:check(R/e['path'],e['sha256'],e['size'])
    put('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bindings),'child_payloads':len(entries),'upstream_bindings':len(refs),'corpus_chunks':20,'reported_statement_reviews':len(coverage),'new_reservations':50,'other_reserved':100,'independent_math_replay':False})
else:raise ValueError('build or verify')
print('PASS',sys.argv[1],len(coverage),'reported reviews',len(entries),'child payloads',len(refs),'input hashes')
