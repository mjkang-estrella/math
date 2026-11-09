from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent; B=L.parent; I=B/'root-mathdb-breadth-intake-r393'; C=B/'pi-mathdb-full-corpus-inventory-r301'
def ref(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
def check(p,e):
 r=ref(p);assert r['sha256']==e['sha256'] and r['size']==e.get('size',e.get('bytes')),str(p);return r
refs={}
def add(p):
 p=p.resolve();refs[str(p)]=ref(p)
for p in I.iterdir():
 if p.is_file():add(p)
for e in json.loads((I/'manifest.json').read_text())['files']:add(I/e['path']);check(I/e['path'],e)
for e in json.loads((I/'bindings.json').read_text()):add(Path(e['original']));check(Path(e['original']),e)
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 add(B/'root-mathdb-accepted-exclusions-r304'/name)
add(B/'root-mathdb-cayley-review-intake-r363'/'disposition.json')
add(C/'manifest.json')
m=json.loads((C/'manifest.json').read_text());print('corpus manifest keys',list(m))
entries=m['files']; chunks=[e for e in entries if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:add(C/e['path']);check(C/e['path'],e)
(L/'input-bindings.json').write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':list(refs.values()),'corpus_chunks':[str(C/e['path']) for e in chunks]},indent=2)+'\n')
r=json.loads((I/'reserved-ids.json').read_text());cov=json.loads((I/'coverage-delta.json').read_text());q=json.loads((I/'queue.json').read_text()); ids=r['ids']
assert len(ids)==len(set(ids))==50 and len(cov)==1233 and r['lane']==L.name
assert set(ids)=={v['mathdb_id'] for v in q}
assert not(set(ids)&(set(map(int,cov))|set(r['other_active_reservations'])|{372627,372628,368940}))
(L/'intake-check.json').write_text(json.dumps({'root_manifest':'verified read-only; upstream verifier not executed','actual_originals_verified':len(refs),'chunks_verified_in_place':20,'assigned_ids':ids,'reviewed_count':len(cov),'active_other_count':len(r['other_active_reservations']),'disjoint':True},indent=2)+'\n')
print('Frozen',len(refs),'refs; exact50 disjoint;20chunks verified')
