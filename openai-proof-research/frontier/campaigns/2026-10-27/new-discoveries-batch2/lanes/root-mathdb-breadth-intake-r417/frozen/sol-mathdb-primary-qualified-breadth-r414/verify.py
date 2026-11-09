from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent;L=R.parent
EXCLUDE={'manifest.json','final-receipt.json'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,e):
 assert p.is_file() and p.stat().st_size==e.get('size',e.get('bytes')) and sha(p)==e['sha256'],str(p)
refs=load(R/'bindings.json')['references']
for e in refs:check(Path(e['path']),e)
I=L/'root-mathdb-breadth-intake-r413';im=load(I/'manifest.json')['files']
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in im}
for e in im:check(I/e['path'],e)
for e in load(I/'bindings.json'):
 check(Path(e['original']),e);check(I/e['copy'],e)
C=L/'pi-mathdb-full-corpus-inventory-r301';chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:check(C/e['path'],e)
r=load(I/'reserved-ids.json');assigned=r['ids'];old=load(I/'coverage-delta.json')
assert len(assigned)==len(set(assigned))==50 and len(old)==1733 and len(set(r['other_active_reservations']))==50
assert not set(assigned)&(set(map(int,old))|set(r['other_active_reservations'])|{372627,372628,368940})
rows=load(R/'dispositions.json');assert len(rows)==50 and {x['mathdb_id'] for x in rows}==set(assigned)
found={}
for e in chunks:
 for line in (C/e['path']).open():
  x=json.loads(line)
  if x['mathdb_id'] in assigned:
   assert x['mathdb_id'] not in found;found[x['mathdb_id']]=x
assert set(found)==set(assigned)
for x in rows:
 o=found[x['mathdb_id']];assert x['literal_statement']==x['scope']==o['statement'] and x['credit']==0
 assert hashlib.sha256(o['statement'].encode()).hexdigest()==x['statement_sha256']
 assert hashlib.sha256(json.dumps(o,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()==x['canonical_record_sha256']
 assert sha(R/x['evidence']['text'])==x['evidence']['text_sha256']
for p in (R/'primary').glob('*.meta.json'):
 m=load(p)
 if 'sha256' in m:check(p.with_name(p.name.removesuffix('.meta.json')),m)
assert load(R/'proposals.json')['proposals']==[]
# Recompute the administrative exact-ID join, including list-valued associations.
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 def hits(o):
  if isinstance(o,dict):
   for k,v in o.items():
    if 'mathdb' in k and (k.endswith('id') or k.endswith('ids')):
     ns=v if isinstance(v,list) else [v]
     for n in ns:
      if str(n).isdigit() and int(n) in assigned:yield int(n)
    yield from hits(v)
  elif isinstance(o,list):
   for v in o:yield from hits(v)
 assert list(hits(load(L/'root-mathdb-accepted-exclusions-r304'/name)))==[]
entries=load(R/'manifest.json')['files'];actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-EXCLUDE
assert len(entries)==len({e['path'] for e in entries}) and actual=={e['path'] for e in entries}
for e in entries:check(R/e['path'],e)
print(json.dumps({'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bound_originals':len(refs),'root_manifest_read_only':True,'upstream_receipt_writes':0,'chunks_verified_in_place':20,'assignment_exactset':50,'reviewed_disjoint':1733,'other_reservation_disjoint':50,'literal_and_canonical_hashes':50,'payload_files':len(entries),'proposals':0,'credit':0,'independent_mathematical_proof_replay':False,'registry':'HOLD'},indent=2))
