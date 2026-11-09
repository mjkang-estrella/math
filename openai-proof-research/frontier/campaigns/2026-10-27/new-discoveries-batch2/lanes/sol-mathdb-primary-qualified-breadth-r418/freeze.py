from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent; L=R.parent; I=L/'root-mathdb-breadth-intake-r417'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ck(p,e):assert p.stat().st_size==e.get('size',e.get('bytes')) and h(p)==e['sha256'],str(p)
refs={}
def add(p,role):
 p=p.resolve(); refs[str(p)]={'path':str(p),'sha256':h(p),'size':p.stat().st_size,'role':role}
add(I/'manifest.json','read-only intake manifest')
m=json.loads((I/'manifest.json').read_text())
files=m['files']; assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in files}
for e in files:ck(I/e['path'],e);add(I/e['path'],'intake manifest payload reference')
add(I/'verification-receipt.json','pre-existing receipt; never execute upstream verifier')
for e in json.loads((I/'bindings.json').read_text()):
 p=Path(e['original']);ck(p,e);ck(I/e['copy'],e);add(p,'intake actual original')
# One explicit flat source binding layer, no recursive expansion or copies.
b=I/'frozen/sol-mathdb-primary-qualified-breadth-r414/bindings.json'
for e in json.loads(b.read_text())['references']:
 p=Path(e['path']);ck(p,e);add(p,'inherited actual immutable reference')
C=L/'pi-mathdb-full-corpus-inventory-r301';add(C/'manifest.json','corpus manifest')
chunks=[e for e in json.loads((C/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:ck(C/e['path'],e);add(C/e['path'],'verified original corpus chunk IN PLACE')
for p in (L/'root-mathdb-accepted-exclusions-r304').iterdir():
 if p.is_file():add(p,'r304 exclusion/history binding')
add(L/'root-mathdb-cayley-review-intake-r363/disposition.json','r363 inherited objection binding')
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 if p.exists():add(p,'campaign administrative context')
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':list(refs.values()),'chunks_verified_in_place':20,'root_manifest_read_only':True,'upstream_receipt_writer_executed':False,'scientific_content_read_before_freeze':False}
(R/'bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('FROZEN',len(refs),'references; 20 original chunks verified; no upstream writes')
