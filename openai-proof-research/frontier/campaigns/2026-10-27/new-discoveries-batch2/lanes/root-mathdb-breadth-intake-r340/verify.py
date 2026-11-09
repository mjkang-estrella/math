from pathlib import Path
import hashlib,json,sys,datetime
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,o):(R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
 for p in [Path(e['original']),R/e['copy']]:
  assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
C=R/'frozen/pi-mathdb-primary-qualified-breadth-r339'
entries=json.loads((C/'manifest.json').read_text())['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in entries}
for e in entries:
 p=C/e['path'];assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
refs=json.loads((C/'bindings.json').read_text())['bindings']
for e in refs:
 p=Path(e['original']);assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
old=json.loads((R/'frozen/root-mathdb-breadth-intake-r338/coverage-delta.json').read_text())
rows=json.loads((C/'dispositions.json').read_text())['dispositions']
ids=[str(x['mathdb_id']) for x in rows]
reserved=json.loads((R/'frozen/root-mathdb-breadth-intake-r338/reserved-ids.json').read_text())['ids']
assert len(old)==283 and len(ids)==len(set(ids))==50 and set(ids)==set(map(str,reserved)) and not(set(ids)&set(old))
coverage=dict(old)
for x in rows:coverage[str(x['mathdb_id'])]={'disposition':x['disposition'],'record_statement_review':'delegate_reported_complete','report':'pi-mathdb-primary-qualified-breadth-r339/dispositions.json','source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0}
queue=[json.loads(s) for s in (R/'frozen/ranked-queue.jsonl').read_text().splitlines()]
selected=[];seen=set(coverage)
for x in queue:
 n=str(x['mathdb_id'])
 if n in seen or x['status']!='open' or x['statement_completeness']!='full':continue
 selected.append(x);seen.add(n)
 if len(selected)==50:break
assert len(selected)==50
def payload():return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
 put('coverage-delta.json',coverage);put('queue.json',selected);put('reserved-ids.json',{'ids':[x['mathdb_id'] for x in selected],'lane':'unassigned_next_breadth','status':'reserved_not_reviewed'})
 put('manifest.json',{'files':[{'path':s,'sha256':sha(R/s),'size':(R/s).stat().st_size} for s in sorted(payload())]})
elif sys.argv[1]=='verify':
 assert json.loads((R/'coverage-delta.json').read_text())==coverage
 assert json.loads((R/'queue.json').read_text())==selected
 own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
 for e in own:
  p=R/e['path'];assert sha(p)==e['sha256'] and p.stat().st_size==e['size'],str(p)
 put('verification-receipt.json',{'status':'PASS','at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bindings),'child_payloads':len(entries),'upstream_actual_hashes':len(refs),'reviewed_ids':len(coverage),'new_reservations':50,'root_payloads':len(own),'math_replay':False})
else:raise ValueError('build or verify')
print('PASS',sys.argv[1],len(coverage),'reported reviews',len(refs),'actual upstream hashes')
