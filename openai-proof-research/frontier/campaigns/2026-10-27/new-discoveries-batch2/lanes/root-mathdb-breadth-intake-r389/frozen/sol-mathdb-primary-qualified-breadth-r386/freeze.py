import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent; R=B/'root-mathdb-circulant-park-intake-r385'; C=B/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def ref(p):
 b=p.read_bytes();return dict(path=str(p.resolve()),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
def check(p,e):
 r=ref(p);assert r['sha256']==e['sha256'] and r['size']==e.get('size',e.get('bytes')),str(p);return r
refs={}
def add(p):refs[str(p.resolve())]=ref(p)
for n in ['manifest.json','bindings.json','coverage-delta.json','queue.json','reserved-ids.json','verification-receipt.json']:add(R/n)
root=load(R/'manifest.json')
for e in root['files']:check(R/e['path'],e)
for e in load(R/'bindings.json'):
 p=pathlib.Path(e['original']);check(p,e);add(p)
for n in ['accepted-exclusions.json','historical-dispositions.json','manifest.json','bindings.json']:add(B/'root-mathdb-accepted-exclusions-r304'/n)
add(B/'root-mathdb-cayley-review-intake-r363/disposition.json');add(C/'manifest.json')
chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(C/e['path'],e);add(C/e['path'])
r=load(R/'reserved-ids.json'); ids=r['ids']; cov=load(R/'coverage-delta.json')
assert len(ids)==len(set(ids))==50 and len(r['other_active_reservations'])==50
assert len(cov)==1033,len(cov)
assert not set(ids)&set(map(int,cov));assert not set(ids)&set(r['other_active_reservations']);assert not set(ids)&{372627,372628,368940}
out=dict(frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),references=list(refs.values()),root_manifest_verified_read_only=True,all_corpus_chunks_verified_in_place=20,reserved_ids=ids,other_active_reservations=r['other_active_reservations'],reviewed_ids=sorted(map(int,cov)))
p=L/'input-bindings.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');p.chmod(0o444)
print('Frozen',len(refs),'flat references; 20 corpus chunks pass; 50 IDs disjoint from 1033 + active + focused.')
