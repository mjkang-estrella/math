from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent; L=R.parent; C=L.parent
I=L/'pi-mathdb-full-corpus-inventory-r301'; T=L/'root-mathdb-breadth-intake-r383'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,x): (R/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
refs={}
def bind(p,h=None,s=None):
 p=Path(p).resolve(); a=sha(p); z=p.stat().st_size
 assert h is None or a==h,str(p)
 assert s is None or z==s,str(p)
 refs[str(p)]={'path':str(p),'sha256':a,'size':z}
 return p
for p in T.iterdir():
 if p.is_file(): bind(p)
for e in json.loads((T/'manifest.json').read_text())['files']: bind(T/e['path'],e['sha256'],e['size'])
for e in json.loads((T/'bindings.json').read_text()):
 bind(e['original'],e['sha256'],e['size']);bind(T/e['copy'],e['sha256'],e['size'])
# Flat references, no historical evidence tree copies.
for e in json.loads((L/'sol-mathdb-primary-qualified-breadth-r380/input-bindings.json').read_text()): bind(e['path'],e['sha256'],e['size'])
bind(I/'manifest.json')
chunks=[e for e in json.loads((I/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks: bind(I/e['path'],e['sha256'],e['bytes'])
for n in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 for p in (L/n).iterdir():
  if p.is_file(): bind(p)
for p in [C/'AGENTS.md',C/'ledger.json',C/'prior-campaign-context.json',C.parents[3]/'AGENTS.md',C.parents[3]/'sources/upstream.json',C.parents[3]/'sources/CONTENTS.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 if p.is_file(): bind(p)
ids=json.loads((T/'reserved-ids.json').read_text())['ids']; coverage=json.loads((T/'coverage-delta.json').read_text())
assert len(ids)==len(set(ids))==50 and len(coverage)==1033
assert not set(map(str,ids))&set(coverage) and not set(ids)&{372627,372628,368940}
put('input-bindings.json',list(refs.values()))
put('freeze-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','root_manifest_read_only':True,'root_verifier_executed':False,'flat_references':len(refs),'corpus_chunks_in_place':20,'reservation':ids,'reported_coverage':1033,'r363_resolution':'exact requested path absent; located root-mathdb-cayley-review-intake-r363 by directory filename before content reading'})
print('FROZEN',len(refs),'references, 20 chunks, 50 disjoint IDs')
