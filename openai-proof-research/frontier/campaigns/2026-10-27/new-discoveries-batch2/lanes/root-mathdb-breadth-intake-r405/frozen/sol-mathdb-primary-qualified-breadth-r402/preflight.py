from pathlib import Path
import json,hashlib,datetime
O=Path(__file__).resolve().parent; L=O.parent; I=L/'root-mathdb-breadth-intake-r401'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_bytes())
def ck(p,r):
 b=p.read_bytes();assert len(b)==r.get('size',r.get('bytes')),str(p)+' size';assert hashlib.sha256(b).hexdigest()==r['sha256'],str(p)+' sha256'
f=load(O/'frozen-references.json'); refs={r['path']:r for r in f['references']}
for p in [I/'manifest.json',I/'bindings.json',I/'coverage-delta.json',I/'queue.json',I/'reserved-ids.json',C/'manifest.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/disposition.json']:ck(p,refs[str(p)])
for r in load(I/'manifest.json')['files']:ck(I/r['path'],r)
for r in load(I/'bindings.json'):ck(Path(r['original']),r);ck(I/r['copy'],r)
chunks=[r for r in load(C/'manifest.json')['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20
for r in chunks:ck(C/r['path'],r)
r=load(I/'reserved-ids.json'); ids=set(r['ids']); old=set(map(int,load(I/'coverage-delta.json'))); assert len(ids)==50 and len(old)==1433;assert not ids&old;assert not ids&set(r['other_active_reservations']);assert not ids&{372627,372628,368940};assert {q['mathdb_id'] for q in load(I/'queue.json')}==ids
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_manifest':'read-only exact file hashes pass','bindings_originals':'pass','corpus_chunks_in_place':20,'assignment':50,'previously_reviewed':1433,'disjoint':True,'upstream_verifier_executed':False}
(O/'preflight-receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
