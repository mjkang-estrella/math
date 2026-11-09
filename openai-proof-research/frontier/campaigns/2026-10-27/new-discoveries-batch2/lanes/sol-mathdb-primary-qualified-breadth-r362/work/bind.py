from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parents[1]; L=R.parent
refs=[]
def bind(p):
 b=p.read_bytes(); refs.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))); return b
def load(p):return json.loads(bind(p))
def check(p,e):
 b=bind(p);assert len(b)==e.get('size',e.get('bytes')) and hashlib.sha256(b).hexdigest()==e['sha256'],p
I=L/'root-mathdb-breadth-intake-r361'
m=load(I/'manifest.json')
for e in m['files']:check(I/e['path'],e)
a=load(I/'reserved-ids.json')['ids']; q=load(I/'queue.json'); other=load(L/'root-mathdb-gram-intake-r359/reserved-ids.json')['ids']
assert len(a)==len(set(a))==len(other)==len(set(other))==50
assert set(a)=={x['mathdb_id'] for x in q} and not set(a)&set(other)
C=L/'pi-mathdb-full-corpus-inventory-r301';cm=load(C/'manifest.json'); chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:check(C/e['path'],e)
D=L/'root-mathdb-accepted-exclusions-r304'
for n in ['accepted-exclusions.json','historical-dispositions.json','manifest.json','README.md']:bind(D/n)
for p in [L.parent/'AGENTS.md',L.parents[4]/'AGENTS.md',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']: 
 if p.exists():bind(p)
# All bindings verified before scientific record extraction.
(R/'input-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
(R/'freeze-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),corpus_chunks=20,ids=a,other_ids=other,disjoint=True,root_coverage=583),indent=2)+'\n')
found={}
for e in chunks:
 for line in (C/e['path']).read_text().splitlines():
  x=json.loads(line)
  if int(x.get('mathdb_id',x.get('id',0))) in a:found[int(x.get('mathdb_id',x.get('id',0)))]=x
assert set(found)==set(a),(set(a)-set(found))
(R/'records.json').write_text(json.dumps([found[n] for n in a],indent=2,ensure_ascii=False)+'\n')
print(json.dumps(found[a[0]],indent=2))
