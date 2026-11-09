"""Independent read-only verifier. Prints receipt; caller may retain it in this lane."""
from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r393';C=B/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(p):
 h=hashlib.sha256();size=0
 with p.open('rb') as f:
  while True:
   b=f.read(1024*1024)
   if not b:break
   h.update(b);size+=len(b)
 return h.hexdigest(),size
def check(p,e):
 h,n=digest(p);assert h==e['sha256'] and n==e.get('size',e.get('bytes')),f'byte mismatch: {p}'
bindings=load(L/'input-bindings.json');flat={r['path']:r for r in bindings['references']}
assert len(flat)==len(bindings['references'])
for r in bindings['references']:check(Path(r['path']),r)
for e in load(I/'manifest.json')['files']:check(I/e['path'],e)
for e in load(I/'bindings.json'):
 check(Path(e['original']),e);check(I/e['copy'],e)
for r in load(L/'primary-bindings.json')['references']:check(Path(r['path']),r)
assert digest(L/'primary/polypartition2.html')==digest(B/'pi-mathdb-primary-qualified-breadth-r335/sources/384757/aimpl-polypartition-p2.html')
chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20 and set(bindings['corpus_chunks'])=={str(C/e['path']) for e in chunks}
for e in chunks:check(C/e['path'],e)
r=load(I/'reserved-ids.json');ids=r['ids'];cov=load(I/'coverage-delta.json');queue=load(I/'queue.json')
assert r['lane']==L.name and len(ids)==len(set(ids))==50 and len(cov)==1233
assert len(r['other_active_reservations'])==len(set(r['other_active_reservations']))==50
assert set(ids)=={q['mathdb_id'] for q in queue} and len(queue)==50
assert not(set(ids)&(set(map(int,cov))|set(r['other_active_reservations'])|{372627,372628,368940}))
saved=load(L/'statements.json');ds=load(L/'dispositions.json');selected=set(ids)
assert len(saved)==len(ds)==50 and {x['record']['mathdb_id'] for x in saved}=={x['mathdb_id'] for x in ds}==selected
originals={}
for e in chunks:
 for n,line in enumerate((C/e['path']).open(),1):
  x=json.loads(line)
  if x['mathdb_id'] in selected:
   assert x['mathdb_id'] not in originals
   originals[x['mathdb_id']]=(x,str(C/e['path']),n)
for x in saved:
 orig,p,n=originals[x['record']['mathdb_id']];assert x['record']==orig and x['corpus_path']==p and x['line']==n
for d in ds:
 orig,p,n=originals[d['mathdb_id']]
 assert d['literal_statement']==orig['statement'] and d['statement_sha256']==hashlib.sha256(orig['statement'].encode()).hexdigest()
 assert d['canonical_url']==orig['canonical_url'] and d['source_url']==orig['source_url']
 assert d['credit']==0 and d['precise_scope'] and d['individual_reason'] and not d['proof_section_read'] and not d['dependency_audit']
 assert d['corpus_reference']=={'path':p,'line':n}
assert load(L/'proposals.json')['proposals']==[]
manifest=load(L/'manifest.json'); entries=manifest['files']; names=[e['path'] for e in entries]
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.relative_to(L).as_posix() not in {'manifest.json','final-receipt.json'}}
assert len(names)==len(set(names)) and actual==set(names),f'payload set mismatch: {actual.symmetric_difference(set(names))}'
for e in entries:check(L/e['path'],e)
print(json.dumps({'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity_status':'PASS','protocol_status':'EXCEPTION_initial_administrative_scientific_summaries_before_freeze','upstream_write':False,'original_references_rehashed':len(flat),'chunks_rehashed_in_place':20,'exact_dispositions':50,'reviewed_disjoint':1233,'other_active_disjoint':50,'special_ids_disjoint':[372627,372628,368940],'payload_files':len(entries),'manifest_sha256':digest(L/'manifest.json')[0],'credit':0},indent=2))
