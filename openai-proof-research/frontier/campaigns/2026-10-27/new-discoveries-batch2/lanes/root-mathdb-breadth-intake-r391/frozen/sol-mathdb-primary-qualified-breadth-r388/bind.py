from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent; L=R.parent; I=L/'root-mathdb-breadth-intake-r387'; C=L/'pi-mathdb-full-corpus-inventory-r301'
refs={}
def bind(p,h=None,s=None):
 p=Path(p); b=p.read_bytes(); d=hashlib.sha256(b).hexdigest()
 if h is not None: assert d==h and len(b)==s,str(p)
 refs[str(p)]={'path':str(p),'sha256':d,'size':len(b)}
 return b
def j(p): return json.loads(bind(p))
m=j(I/'manifest.json')['files']; assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in m}
for e in m: bind(I/e['path'],e['sha256'],e['size'])
for e in j(I/'bindings.json'): bind(e['original'],e['sha256'],e['size']); bind(I/e['copy'],e['sha256'],e['size'])
for e in j(L/'sol-mathdb-primary-qualified-breadth-r384/input-bindings.json'): bind(e['path'],e['sha256'],e['size'])
chunks=[e for e in j(C/'manifest.json')['files'] if e['path'].startswith('corpus/')]; assert len(chunks)==20
for e in chunks: bind(C/e['path'],e['sha256'],e['bytes'])
for f in ['accepted-exclusions.json','historical-dispositions.json']: bind(L/'root-mathdb-accepted-exclusions-r304'/f)
bind(L/'root-mathdb-cayley-review-intake-r363/disposition.json')
r=j(I/'reserved-ids.json'); old=j(I/'coverage-delta.json'); q=j(I/'queue.json')
assert len(old)==1083 and len(r['ids'])==len(set(r['ids']))==50 and len(set(r['other_active_reservations']))==50
assert not set(map(str,r['ids'])) & (set(old)|set(map(str,r['other_active_reservations']))|{'372627','372628','368940'})
(R/'input-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(R/'binding-receipt.json').write_text(json.dumps({'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':len(refs),'chunks_in_place':20,'reviewed_ids':1083,'reserved_ids':50,'other_active_ids':50,'copies_created':0},indent=2)+'\n')
print('BOUND',len(refs),'references; intake exact payload verified, all 20 original chunks verified')
