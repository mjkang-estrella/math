from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent; L=R.parent; I=L/'root-mathdb-breadth-intake-r411'
refs={}
def bind(p,role,expected=None):
 p=Path(p).resolve(); b=p.read_bytes(); h=hashlib.sha256(b).hexdigest(); s=len(b)
 if expected:
  assert h==expected['sha256'] and s==expected.get('size',expected.get('bytes')),str(p)
 refs[str(p)]={'path':str(p),'sha256':h,'size':s,'role':role}
def manifest(d):
 p=d/'manifest.json'; bind(p,'manifest')
 for e in json.loads(p.read_text())['files']:bind(d/e['path'],'manifest_payload',e)
manifest(I)
for e in json.loads((I/'bindings.json').read_text()):bind(e['original'],'actual_intake_original',e)
# Follow only the explicit flat upstream reference list, never a historical tree.
P=L/'sol-mathdb-primary-qualified-breadth-r408/bindings.json'
bind(P,'previous_flat_binding')
for e in json.loads(P.read_text())['references']:bind(e['path'],'inherited_actual_original',e)
C=L/'pi-mathdb-full-corpus-inventory-r301';bind(C/'manifest.json','corpus_manifest')
chunks=[e for e in json.loads((C/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:bind(C/e['path'],'in_place_corpus_chunk',e)
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/name
 for p in d.iterdir():
  if p.is_file():bind(p,'accepted_history_or_cayley_boundary')
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 if p.exists():bind(p,'campaign_context')
out={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':sorted(refs.values(),key=lambda e:e['path']),'root_verification':'manifest hashes read-only; upstream verify.py NOT executed (it writes receipt)','corpus_chunks_verified_in_place':20,'recursive_expansion':False}
(R/'bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('FROZEN',len(refs),'references; twenty chunks verified in place')
