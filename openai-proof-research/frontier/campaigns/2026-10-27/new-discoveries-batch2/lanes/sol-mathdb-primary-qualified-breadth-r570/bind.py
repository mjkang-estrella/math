from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parent; L=D.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r569'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def binding(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
refs={}
def bind(p):
 p=p.resolve();r=binding(p);refs[str(p)]=r;return r
def check(p,e):
 r=bind(p);assert r['size']==e.get('size',e.get('bytes')) and r['sha256']==e['sha256'],str(p)
assert bind(I/'manifest.json')['sha256']=='965e8fec63f9c16a1cdae1854dc427bdb5c4bf1c7134fe51fda00e230719a3df'
m=load(I/'manifest.json'); expected={e['path'] for e in m['files']}
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected|set(m['excluded_exact_paths'])
for e in m['files']:check(I/e['path'],e)
bind(I/'verification-receipt.json')
for e in load(I/'bindings.json'):
 check(Path(e['original']),e);check(Path(e['copy']),e)
cm=load(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
(D/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
q=load(I/'queue.json');res=load(I/'reserved-ids.json');ids=set(res['ids']);cov=set(map(int,load(I/'coverage-delta.json')))
assert len(ids)==50 and ids=={r['mathdb_id'] for r in q} and len(cov)==5183 and not ids&cov
sets=[set(x['ids']) for x in load(I/'active-breadth-reservations.json')];assert sum(s==ids for s in sets)==1
protected={337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439,344924}
for j,s in enumerate(sets):
 assert len(s)==50 and not s&cov and not s&protected
 for t in sets[:j]:assert not s&t
out=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if int(r.get('id',r.get('mathdb_id',-1))) in ids:out.append(dict(chunk=str(p),line=n,record=r,canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
assert len(out)==50
(D/'assigned-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
(D/'intake-check.json').write_text(json.dumps(dict(status='PASS_INTEGRITY_ONLY',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),intake_manifest=refs[str(I/'manifest.json')],original_copy_pairs=len(load(I/'bindings.json')),corpus_chunks=20,frozen_inputs=8,coverage_records=5183,reserved_sets=len(sets),assignment_records=50),indent=2)+'\n')
print('PASS',len(refs),len(out));print(json.dumps(out[0],ensure_ascii=False)[:1600])
