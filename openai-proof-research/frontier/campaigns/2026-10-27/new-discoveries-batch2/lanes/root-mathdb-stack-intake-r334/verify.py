from pathlib import Path
import hashlib, json, sys, datetime
R = Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def put(name, obj): (R/name).write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n')
def payload(root): return {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()} - {'manifest.json','verification-receipt.json'}
bindings=json.loads((R/'bindings.json').read_text())['bindings']
for row in bindings:
    for p in [Path(row['original']), R/row['copy']]:
        assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'], str(p)
C=R/'frozen/pi-restricted-stack-periodicity-hypothesis-r329'
m=json.loads((C/'manifest.json').read_text())
assert payload(C)=={e['path'] for e in m['files']}
for e in m['files']:
    p=C/e['path']; assert sha(p)==e['sha256'] and p.stat().st_size==e['size'], str(p)
coverage=json.loads((R/'frozen/root-mathdb-breadth-intake-r332/coverage-delta.json').read_text())
assert len(coverage)==233 and '347483' in coverage
queue=[json.loads(s) for s in (R/'frozen/root-mathdb-breadth-intake-r326/frozen/pi-mathdb-full-corpus-inventory-r301/tags/review-queue-top.jsonl').read_text().splitlines()]
selected=[]; seen=set(coverage)
for row in queue:
    n=str(row['mathdb_id'])
    if n in seen or row['statement_completeness']!='full' or row['status']!='open': continue
    selected.append(row); seen.add(n)
    if len(selected)==50: break
assert len(selected)==50
if sys.argv[1]=='build':
    put('reserved-ids.json', {'lane':'pi-mathdb-primary-qualified-breadth-r335','status':'reserved_not_reviewed','ids':[r['mathdb_id'] for r in selected]})
    put('queue.json',selected)
    put('coverage-status.json',{'reported_statement_reviews':233,'known_ids':95675,'without_reported_review':95442,'new_reservations':50,'acceptance_counts':{'additional':9,'total':39,'next':40},'stack_id':347483,'stack_disposition':'PARK_UNRESOLVED','prior_status':'bounded_search_only','mathematics':'delegate_reported_finite_evidence_not_root_replayed'})
    put('manifest.json',{'files':[{'path':s,'sha256':sha(R/s),'size':(R/s).stat().st_size} for s in sorted(payload(R))]})
elif sys.argv[1]=='verify':
    reserved=json.loads((R/'reserved-ids.json').read_text())['ids']
    assert reserved==[r['mathdb_id'] for r in selected]
    assert len(set(reserved))==50 and not(set(map(str,reserved)) & set(coverage))
    own=json.loads((R/'manifest.json').read_text())['files']
    assert payload(R)=={e['path'] for e in own}
    for e in own:
        p=R/e['path']; assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
    put('verification-receipt.json',{'status':'PASS','checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bindings':len(bindings),'child_payloads':len(m['files']),'root_payloads':len(own),'disjoint_reserved_ids':50,'mathematical_replay':False})
else: raise ValueError('build or verify')
print('PASS',sys.argv[1], 'bindings',len(bindings),'child payloads',len(m['files']))
