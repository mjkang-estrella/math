from pathlib import Path
import hashlib,json,sys,datetime
R=Path(__file__).resolve().parent;L=R.parent
C=R/'frozen/sol-mathdb-cayley-formal-prior-review-r358'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s): assert p.stat().st_size==s and sha(p)==h,str(p)
def put(n,o): (R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
    check(Path(e['original']),e['sha256'],e['size']);check(R/e['copy'],e['sha256'],e['size'])
entries=json.loads((C/'manifest.json').read_text())['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}==set(entries)
for n,e in entries.items(): check(C/n,e['sha256'],e['size'])
refs=json.loads((C/'freeze.json').read_text())['bindings']
for e in refs: check(L/e['path'],e['sha256'],e['size'])
coverage=json.loads((R/'frozen/root-mathdb-breadth-intake-r361/coverage-delta.json').read_text())
held=json.loads((R/'frozen/root-mathdb-breadth-intake-r361/reserved-ids.json').read_text())['ids']
held += json.loads((R/'frozen/root-mathdb-gram-intake-r359/reserved-ids.json').read_text())['ids']
assert len(coverage)==583 and len(held)==len(set(held))==100 and not set(map(str,held))&set(coverage)
queue=[json.loads(s) for s in (R/'frozen/root-mathdb-breadth-intake-r326/frozen/pi-mathdb-full-corpus-inventory-r301/tags/review-queue-top.jsonl').read_text().splitlines()]
selected=[];seen=set(coverage)|set(map(str,held))
for x in queue:
    n=str(x['mathdb_id'])
    if n in seen or x['status']!='open' or x['statement_completeness']!='full': continue
    selected.append(x);seen.add(n)
    if len(selected)==50: break
assert len(selected)==50
reservation={'ids':[x['mathdb_id'] for x in selected],'lane':'sol-mathdb-primary-qualified-breadth-r364','status':'reserved_not_reviewed','other_active_reservation':'root-mathdb-breadth-intake-r361/reserved-ids.json'}
def payload(): return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
    put('coverage-delta.json',coverage);put('queue.json',selected);put('reserved-ids.json',reservation)
    put('manifest.json',{'files':[{'path':n,'sha256':sha(R/n),'size':(R/n).stat().st_size} for n in sorted(payload())]})
elif sys.argv[1]=='verify':
    assert json.loads((R/'coverage-delta.json').read_text())==coverage
    assert json.loads((R/'queue.json').read_text())==selected
    assert json.loads((R/'reserved-ids.json').read_text())==reservation
    own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
    for e in own: check(R/e['path'],e['sha256'],e['size'])
    put('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bindings),'child_payloads':len(entries),'upstream_bindings':len(refs),'reported_statement_reviews':583,'new_disjoint_reservations':50,'other_reserved_ids':100,'independent_math_replay':False,'credit':0})
else: raise ValueError('build or verify')
print('PASS',sys.argv[1],len(entries),'child payloads',len(refs),'upstream bindings; 50 new disjoint reservations')
