from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent; B=L.parent
bindings=[]
def bind(p,h=None,n=None):
 p=Path(p); raw=p.read_bytes(); d=hashlib.sha256(raw).hexdigest()
 assert h is None or h==d, str(p)+' hash mismatch'
 assert n is None or n==len(raw), str(p)+' size mismatch'
 bindings.append(dict(path=str(p),sha256=d,bytes=len(raw)))
 return raw
def load(p):return json.loads(Path(p).read_text())
def manifest(name):
 root=B/name; m=json.loads(bind(root/'manifest.json'))
 for e in (m if isinstance(m,list) else m['files']):
  bind(root/e['path'],e['sha256'],e.get('size',e.get('bytes')))
 return m
# No upstream code execution; only flat manifest members and direct intake binding originals.
m=manifest('root-mathdb-breadth-intake-r455')
for e in load(B/'root-mathdb-breadth-intake-r455/bindings.json'):
 bind(e['original'],e['sha256'],e.get('size',e.get('bytes')))
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:manifest(name)
I=B/'pi-mathdb-full-corpus-inventory-r301'; im=json.loads(bind(I/'manifest.json'))
chunks=[e for e in im['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:bind(I/e['path'],e['sha256'],e['bytes'])
for e in im['frozen_inputs']:bind(I/e['path'],e['sha256'],e['bytes'])
(L/'inventory-frozen-membership.json').write_text(json.dumps(im['frozen_inputs'],indent=2)+'\n')
R=B/'root-mathdb-breadth-intake-r455'; r=load(R/'reserved-ids.json');q=load(R/'queue.json');c=load(R/'coverage-delta.json')
assert len(c)==2783
ids=r['ids']; assert len(ids)==len(set(ids))==50 and ids==[x['mathdb_id'] for x in q]
assert not set(ids)&(set(r['other_active_reservations'])|set(map(int,c))|{372627,372628,368940,404067,364119})
# Freeze metadata references and hashes before scientific/history reading.
uniq={e['path']:e for e in bindings}
(L/'bindings.json').write_text(json.dumps(list(uniq.values()),indent=2)+'\n')
(L/'preflight.json').write_text(json.dumps(dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),chunks=20,intake_manifest_members=len(m['files']),flat_references=len(uniq),assigned=50,baseline_reported_reviews=2783,upstream_code_executed=False),indent=2)+'\n')
print('PASS: independent bytes/hash checks; 20 in-place chunks; intake originals; exclusions bound; assignment/prior coverage disjoint.')
