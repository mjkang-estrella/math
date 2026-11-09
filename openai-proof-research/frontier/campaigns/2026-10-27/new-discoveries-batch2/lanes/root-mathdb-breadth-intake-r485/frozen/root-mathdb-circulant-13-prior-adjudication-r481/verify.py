from pathlib import Path
import hashlib,json,sys,datetime
R=Path(__file__).resolve().parent;L=R.parent
C=R/'frozen/sol-mathdb-primary-qualified-breadth-r476'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s): assert p.stat().st_size==s and sha(p)==h,str(p)
def put(n,o): (R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
    check(Path(e['original']),e['sha256'],e.get('size',e.get('bytes')));check(R/e['copy'],e['sha256'],e.get('size',e.get('bytes')))
child_manifest=json.loads((C/'manifest.json').read_text())
assert set(child_manifest['excluded_paths'])=={'manifest.json','final-receipt.jsonl'} and len(child_manifest['excluded_paths'])==2
entries=child_manifest['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.jsonl'}=={e['path'] for e in entries}
for e in entries: check(C/e['path'],e['sha256'],e.get('size',e.get('bytes')))
refs=json.loads((C/'flat-bindings.json').read_text())
for e in refs: check(Path('/home/mj-kang/Documents/Dev/math')/e['path'],e['sha256'],e.get('size',e.get('bytes')))
I=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in json.loads((I/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
frozen_entries=json.loads((I/'manifest.json').read_text())['frozen_inputs']
assert len(frozen_entries)==8
for e in frozen_entries: check(I/e['path'],e['sha256'],e['bytes'])
for e in chunks: check(I/e['path'],e['sha256'],e['bytes'])
old=json.loads((R/'frozen/root-mathdb-breadth-intake-r479/coverage-delta.json').read_text())
reserved=json.loads((R/'frozen/root-mathdb-breadth-intake-r475/reserved-ids.json').read_text())['ids']
rows=json.loads((C/'dispositions.json').read_text());ids=[str(x['mathdb_id']) for x in rows]
assert len(old)==3283 and len(ids)==len(set(ids))==50 and set(ids)==set(map(str,reserved)) and not set(ids)&set(old)
found={}
for e in chunks:
    with (I/e['path']).open() as f:
        for line in f:
            x=json.loads(line);n=str(x['mathdb_id'])
            if n in ids:
                assert n not in found;found[n]=x
assert set(found)==set(ids)
for x in rows:
    original=found[str(x['mathdb_id'])]
    assert x['literal_statement']==original['statement'] and x['accepted_credit']==0
    assert hashlib.sha256(x['literal_statement'].encode()).hexdigest()==x['statement_utf8_sha256']
    assert hashlib.sha256(json.dumps(original,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()==x['canonical_record_sha256']
assert json.loads((C/'proposals.json').read_text())==[]
receipt_lines=[json.loads(z) for z in (C/'final-receipt.jsonl').read_text().splitlines()]
receipt=receipt_lines[0]
assert receipt['integrity']=='PASS' and receipt['math_pass'] is False and receipt['novelty_pass'] is False
assert receipt_lines[1]['guard_exit']==0
assert receipt['manifest_sha256']==sha(C/'manifest.json')
coverage=dict(old)
for x in rows:
    coverage[str(x['mathdb_id'])]={'disposition':x['disposition'],'record_statement_review':'delegate_reported_complete','report':'sol-mathdb-primary-qualified-breadth-r476/dispositions.json','proof_dependency_scope_reported':'no_complete_dependency_audit','source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0,'evidence_level_reported':{k:x[k] for k in ('source','proof','registry','successor_review')},'scope_discipline_limit':'Forty-eight target and four successor PDFs; selected passages, no whole-body or complete dependency audit. Five exact public statement matches and one substantive-range match with boundary held. Root reconciles integrity only.'}
held=json.loads((R/'frozen/root-mathdb-breadth-intake-r479/reserved-ids.json').read_text())['ids']
assert len(set(held))==50 and not set(map(str,held))&set(coverage)
queue=[json.loads(s) for s in (R/'frozen/root-mathdb-breadth-intake-r415/routing-queue.jsonl').read_text().splitlines()]
selected=[];seen=set(coverage)|set(map(str,held))
for x in queue:
    n=str(x['mathdb_id'])
    if n in seen or x['status']!='open' or x['statement_completeness']!='full':continue
    selected.append(x);seen.add(n)
    if len(selected)==100:break
assert len(selected)==100
second=selected[50:];selected=selected[:50]
reservation={'ids':[x['mathdb_id'] for x in selected],'lane':'sol-mathdb-primary-qualified-breadth-r482','status':'reserved_not_reviewed','other_active_reservations':held+[x['mathdb_id'] for x in second]}
second_reservation={'ids':[x['mathdb_id'] for x in second],'lane':'sol-mathdb-primary-qualified-breadth-r484','status':'reserved_not_reviewed','other_active_reservations':held+reservation['ids']}
assert len(set(reservation['ids']+second_reservation['ids']+held))==150
V=R/'frozen/sol-mathdb-circulant-13-prior-bridge-review-r478'
vm=json.loads((V/'manifest.json').read_text());vfiles=vm['files']
assert len(vfiles)==18 and {e['path'] for e in vfiles}=={str(p.relative_to(V)) for p in V.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'}
for e in vfiles:check(V/e['path'],e['sha256'],e['size'])
vrefs=[]
for name in ['input-bindings.json','additional-bindings.json']:vrefs.extend(json.loads((V/name).read_text()))
assert len(vrefs)==321
for e in vrefs:check(Path(e['path']),e['sha256'],e['size'])
vr=json.loads((V/'final-receipt.json').read_text());assert vr['status']=='PASS' and vr['manifest_sha256']==sha(V/'manifest.json')

def payload():return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
    put('coverage-delta.json',coverage);put('queue.json',selected);put('reserved-ids.json',reservation);put('queue-r484.json',second);put('reserved-ids-r484.json',second_reservation)
    put('manifest.json',{'files':[{'path':s,'sha256':sha(R/s),'size':(R/s).stat().st_size} for s in sorted(payload())]})
elif sys.argv[1]=='verify':
    assert json.loads((R/'coverage-delta.json').read_text())==coverage
    assert json.loads((R/'queue-r484.json').read_text())==second and json.loads((R/'reserved-ids-r484.json').read_text())==second_reservation
    assert json.loads((R/'queue.json').read_text())==selected and json.loads((R/'reserved-ids.json').read_text())==reservation
    own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
    for e in own:check(R/e['path'],e['sha256'],e.get('size',e.get('bytes')))
    put('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bindings),'child_payloads':len(entries),'upstream_bindings':len(refs),'corpus_chunks':20,'reported_statement_reviews':len(coverage),'new_reservations':100,'focused_review_payloads':len(vfiles),'focused_review_references':len(vrefs),'other_reserved':len(held),'independent_math_replay':False})
else:raise ValueError('build or verify')
print('PASS',sys.argv[1],len(coverage),'reported reviews',len(entries),'child payloads',len(refs),'input hashes')
