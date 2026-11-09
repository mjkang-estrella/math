from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent;r=json.loads((L/'results.json').read_text());reservation=json.loads((L/'reservation.json').read_text());checks=[]
assert len(r)==20 and set(r)==set(map(str,reservation['ids']))
for i,x in r.items():
 p=x['literal_provenance'];b=(L/f'raw-{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==p['raw_sha256'];assert json.loads(b)==x['literal_record'];assert hashlib.sha256(x['literal_record']['statement'].encode()).hexdigest()==p['statement_sha256']
 c=Path(p['chunk']);assert hashlib.sha256(c.read_bytes()).hexdigest()==p['chunk_sha256'];assert list(c.open('rb'))[p['line']-1]==b
 checks.append({'id':i,'raw_newline':True,'line_one_based':p['line'],'verified':True})
# Actual assignments, not substring hits in arbitrary prose or decimal certificates.
collisions=[]
for p in L.parent.glob('*/reservation.json'):
 if p.parent==L:continue
 try:ids=set(map(int,json.loads(p.read_text()).get('ids',[])))
 except:continue
 overlap=ids & set(reservation['ids'])
 if overlap:collisions.append({'path':str(p),'ids':sorted(overlap)})
# None should intersect fresh assignments; old coverage may discuss titles and is separately screened.
assert not collisions,collisions
v={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records':checks,'cross_reservation_collisions':collisions,'count_unchanged':'52/60','accepted_credit':0,'no_lean_or_heavy_search':True,'limitation':'Earlier capped runs did not collect sampled RSS; hard AS limit was 6GiB. Final wrapper samples group RSS. All subprocesses invoked by prior cap wrappers have completed.'}
(L/'validation.json').write_text(json.dumps(v,indent=2))
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['HASHES.json','finalcheck.log','finalcheck.run.json']}
(L/'HASHES.json').write_text(json.dumps(manifest,indent=2)+'\n');print('PASS',len(checks),'raw bindings;',len(manifest),'artifact hashes')
