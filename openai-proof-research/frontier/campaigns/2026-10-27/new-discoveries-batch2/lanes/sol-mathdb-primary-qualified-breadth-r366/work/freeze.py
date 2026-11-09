from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parents[1]; L=R.parent; refs={}
def bind(p):
 b=p.read_bytes(); refs[str(p)]={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)};return b
def load(p):return json.loads(bind(p))
def check(p,e):
 b=bind(p);assert len(b)==e.get('size',e.get('bytes')) and hashlib.sha256(b).hexdigest()==e['sha256'],p
I=L/'root-mathdb-breadth-intake-r365'
for e in load(I/'manifest.json')['files']:check(I/e['path'],e)
# Verify all original references bound by intake, without copying history.
for e in load(I/'bindings.json'):check(Path(e['original']),e)
prior=load(L/'sol-mathdb-primary-qualified-breadth-r362/input-bindings.json')
for e in prior:
 if any(t in e['path'] for t in ['pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304']):check(Path(e['path']),e)
a=load(I/'reserved-ids.json')['ids'];q=load(I/'queue.json');cov=load(I/'coverage-delta.json')
sets=[a]+[load(L/n/'reserved-ids.json')['ids'] for n in ['root-mathdb-gram-intake-r359','root-mathdb-cayley-review-intake-r363']]
assert all(len(s)==len(set(s))==50 for s in sets)
assert len(set(sum(sets,[])))==150 and set(a)=={x['mathdb_id'] for x in q}
assert len(cov)==633 and not set(map(str,a))&set(cov)
C=L/'pi-mathdb-full-corpus-inventory-r301'; chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:check(C/e['path'],e)
D=L/'root-mathdb-accepted-exclusions-r304'
for e in load(D/'manifest.json'):assert hashlib.sha256(bind(D/e['path'])).hexdigest()==e['sha256']
for n in ['accepted-exclusions.json','historical-dispositions.json','README.md']:bind(D/n)
for n in ['manifest.json','disposition.json','DECISION.md']:bind(L/'root-mathdb-cayley-review-intake-r363'/n)
for p in [L.parent/'AGENTS.md',L.parents[4]/'AGENTS.md',L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L.parents[4]/'sources/upstream.json',L.parents[4]/'sources/CONTENTS.md']: 
 if p.exists():bind(p)
bind(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
(R/'input-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(R/'freeze-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),corpus_chunks=20,sets=sets,disjoint=True,root_coverage=633,input_files=len(refs)),indent=2)+'\n')
found={}
for e in chunks:
 for line in (C/e['path']).read_text().splitlines():
  x=json.loads(line);n=int(x.get('mathdb_id',x.get('id',0)))
  if n in a:found[n]=x
assert set(found)==set(a)
(R/'records.json').write_text(json.dumps([found[n] for n in a],indent=2,ensure_ascii=False)+'\n')
for n in a:
 x=found[n]; print(n,x['title']); print(x['statement']); print('SOURCE',x.get('sources',x.get('references','')), '\n')
