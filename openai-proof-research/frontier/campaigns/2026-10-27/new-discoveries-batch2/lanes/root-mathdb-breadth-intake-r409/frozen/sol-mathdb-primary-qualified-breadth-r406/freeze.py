from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent; B=L.parent; I=B/'root-mathdb-breadth-intake-r405'; C=B/'pi-mathdb-full-corpus-inventory-r301'
def ref(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
refs={}
def add(p):
 r=ref(p);refs[str(p)]=r;return r
def check(p,r):
 a=add(p);assert a['sha256']==r['sha256'] and a['size']==r.get('size',r.get('bytes')),str(p)
for n in ['manifest.json','bindings.json','coverage-delta.json','queue.json','reserved-ids.json']:add(I/n)
for r in json.loads((I/'manifest.json').read_text())['files']:check(I/r['path'],r)
for r in json.loads((I/'bindings.json').read_text()):check(Path(r['original']),r)
add(C/'manifest.json');cm=json.loads((C/'manifest.json').read_text()); chunks=[r for r in cm['files'] if r['path'].startswith('corpus/') and r['path'].endswith('.jsonl')];assert len(chunks)==20,len(chunks)
for r in chunks:check(C/r['path'],r)
for n in ['manifest.json','bindings.json','accepted-exclusions.json','historical-dispositions.json']:add(B/'root-mathdb-accepted-exclusions-r304'/n)
add(B/'root-mathdb-cayley-review-intake-r363'/'disposition.json')
for p in [B.parent/'ledger.json',B.parent/'prior-campaign-context.json',B.parents[3]/'sources/upstream.json',B.parents[3]/'sources/CONTENTS.md']:
 if p.exists():add(p)
(L/'frozen-references.json').write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':list(refs.values()),'corpus_chunks':[str(C/r['path']) for r in chunks],'root_manifest_verified_read_only':True},indent=2)+'\n')
print('Frozen',len(refs),'flat references; verified 20 chunks and root manifest/original bindings read-only')
