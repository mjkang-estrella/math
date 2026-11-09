from pathlib import Path
import json,hashlib,datetime
O=Path(__file__).resolve().parent;L=O.parent;R=L/'root-mathdb-breadth-intake-r399';I=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,r):
 b=p.read_bytes();assert sha(b)==r['sha256'],('SHA256',str(p));n=r.get('size',r.get('bytes'));assert n is None or n==len(b),('size',str(p))
def load(p):return json.loads(p.read_text())
refs=0
for f in ['initial-freeze.json','input-bindings.json']:
 assert O.joinpath(f).stat().st_mode & 0o222 ==0,('mutable freeze',f)
 for r in load(O/f)['refs']:check(Path(r['path']),r);refs+=1
for r in load(R/'manifest.json')['files']:check(R/r['path'],r)
for r in load(R/'bindings.json'):check(Path(r['original']),r)
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 for r in load(L/name/'bindings.json'):check(Path(r['original']),r)
chunkrefs=[r for r in load(I/'manifest.json')['files'] if r['path'].startswith('corpus/mathdb-normalized-chunk-') and r['path'].endswith('.jsonl')];assert len(chunkrefs)==20
assert set(load(O/'input-bindings.json')['chunks'])=={str(I/r['path']) for r in chunkrefs}
for r in chunkrefs:check(I/r['path'],r)
a=load(R/'reserved-ids.json');ids=set(a['ids']);assert len(a['ids'])==len(ids)==50 and a['lane']==O.name
c=load(R/'coverage-delta.json');assert len(c)==1383;assert not ids.intersection(map(int,c));assert len(a['other_active_reservations'])==50;assert not ids.intersection(a['other_active_reservations']);assert not ids.intersection([372627,372628,368940])
records=load(O/'records.json');disps=load(O/'dispositions.json');assert len(records)==len(disps)==50
assert {r['record']['mathdb_id'] for r in records}==ids;assert {r['mathdb_id'] for r in disps}==ids
found={}
for cr in chunkrefs:
 p=I/cr['path']
 with p.open('rb') as f:
  for line in f:
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    i=r['mathdb_id'];assert i not in found;found[i]=(r,sha(line),str(p))
assert set(found)==ids
for x in records:
 r,h,p=found[x['record']['mathdb_id']];assert x['record']==r and x['line_sha256']==h and x['chunk']==p
 canon=sha(json.dumps(r,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode());assert x['canonical_sha256']==canon
 d=next(d for d in disps if d['mathdb_id']==r['mathdb_id']);assert d['literal_statement']==r['statement'] and d['statement_sha256']==sha(r['statement'].encode()) and d['canonical_record_sha256']==canon and d['source_line_sha256']==h
 assert d['accepted_credit']==0 and not d['current_registry_clearance']
assert load(O/'proposals.json')==[]
m=load(O/'manifest.json');actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'}
assert actual=={r['path'] for r in m['files']} and len(actual)==len(m['files']),('payload exactset',actual.symmetric_difference({r['path'] for r in m['files']}))
for r in m['files']:check(O/r['path'],r)
print(json.dumps({'pass':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_reference_checks':refs,'root_manifest_readonly':True,'twenty_chunks_in_place':20,'exact_assignment':50,'reviewed_disjoint':1383,'other_active_reservation_disjoint':50,'statement_canonical_line_hashes':50,'payload_exactset_files':len(actual),'credit_delta':0,'upstream_writes':0},indent=2))
