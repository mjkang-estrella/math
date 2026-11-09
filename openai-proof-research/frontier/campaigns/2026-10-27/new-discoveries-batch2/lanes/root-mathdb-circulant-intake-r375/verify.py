from pathlib import Path
import hashlib,json,sys,datetime
R=Path(__file__).resolve().parent;L=R.parent
C=R/'frozen/claude-mathdb-primary-qualified-breadth-r360'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s):assert p.stat().st_size==s and sha(p)==h,str(p)
def put(n,o):(R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
    check(Path(e['original']),e['sha256'],e['size']);check(R/e['copy'],e['sha256'],e['size'])
entries=json.loads((C/'manifest.json').read_text())['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in entries}
for e in entries:check(C/e['path'],e['sha256'],e['size'])
refs=json.loads((C/'input-bindings.json').read_text())
for e in refs:check(Path(e['path']),e['sha256'],e['size'])
I=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in json.loads((I/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(I/e['path'],e['sha256'],e['bytes'])
old=json.loads((R/'frozen/root-mathdb-breadth-intake-r373/coverage-delta.json').read_text())
reserved=json.loads((R/'frozen/root-mathdb-gram-intake-r359/reserved-ids.json').read_text())['ids']
rows=json.loads((C/'dispositions.json').read_text())['dispositions'];ids=[str(x['mathdb_id']) for x in rows]
assert len(old)==833 and len(ids)==len(set(ids))==50 and set(ids)==set(map(str,reserved)) and not set(ids)&set(old)
records={str(x['mathdb_id']):x for x in json.loads((C/'records.json').read_text())}
found={}
for e in chunks:
    with (I/e['path']).open() as f:
        for line in f:
            x=json.loads(line);n=str(x['mathdb_id'])
            if n in ids:
                assert n not in found;found[n]=x
assert set(found)==set(records)==set(ids)
for x in rows:
    n=str(x['mathdb_id']);assert records[n]['statement']==found[n]['statement']
    assert x['literal_statement_sha256']==hashlib.sha256(found[n]['statement'].encode()).hexdigest() and x['accepted_credit']==0
proposals=json.loads((C/'proposals.json').read_text())['proposals']
assert {x['mathdb_id'] for x in proposals}=={368940,372627,372628}
coverage=dict(old)
for x in rows:coverage[str(x['mathdb_id'])]={'disposition':x['disposition'],'record_statement_review':'delegate_reported_complete','report':'claude-mathdb-primary-qualified-breadth-r360/dispositions.json','primary_body_review_reported':x['primary_body_review'],'source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0}
held=[]
for n in ['root-mathdb-breadth-intake-r373','root-mathdb-breadth-intake-r371']:
    held+=json.loads((R/'frozen'/n/'reserved-ids.json').read_text())['ids']
assert len(held)==len(set(held))==100 and not set(map(str,held))&set(coverage)
def payload():return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
    put('coverage-delta.json',coverage)
    put('manifest.json',{'files':[{'path':s,'sha256':sha(R/s),'size':(R/s).stat().st_size} for s in sorted(payload())]})
elif sys.argv[1]=='verify':
    assert json.loads((R/'coverage-delta.json').read_text())==coverage
    own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
    for e in own:check(R/e['path'],e['sha256'],e['size'])
    put('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bindings),'child_payloads':len(entries),'upstream_bindings':len(refs),'corpus_chunks':20,'reported_statement_reviews':len(coverage),'pending_proposals':3,'other_reserved':100,'independent_math_replay':False})
else:raise ValueError('build or verify')
print('PASS',sys.argv[1],len(coverage),'reported reviews',len(entries),'child payloads',len(refs),'input hashes')
