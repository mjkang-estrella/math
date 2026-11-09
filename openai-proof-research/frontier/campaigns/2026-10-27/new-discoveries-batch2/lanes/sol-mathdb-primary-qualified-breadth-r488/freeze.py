from pathlib import Path
import json,hashlib
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2');L=B/'lanes';O=L/'sol-mathdb-primary-qualified-breadth-r488';I=L/'root-mathdb-breadth-intake-r487'; C=L/'pi-mathdb-full-corpus-inventory-r301'
refs={}
def bind(p,expected=None):
 p=p.resolve();b=p.read_bytes();v={'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if expected: assert v['size']==expected.get('size',expected.get('bytes')) and v['sha256']==expected['sha256'],str(p)
 refs[str(p)]=v
 return b
# Freeze intake before interpreting any scientific/admin payload.
m=json.loads(bind(I/'manifest.json'))
actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
assert actual=={x['path'] for x in m['files']}
for x in m['files']:bind(I/x['path'],x)
bind(I/'verification-receipt.json')
for x in json.loads((I/'bindings.json').read_text()):
 bind(Path(x['original']),x);bind(Path(x['copy']),x)
cm=json.loads(bind(C/'manifest.json'));chunks=[x for x in cm['files'] if x['path'].startswith('corpus/')]
assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for x in chunks+cm['frozen_inputs']:bind(C/x['path'],x)
for name in ['accepted-exclusions.json','historical-dispositions.json']:bind(L/'root-mathdb-accepted-exclusions-r304'/name)
for p in L.glob('*r363/DECISION.md'):bind(p)
for p in [B/'ledger.json',B/'prior-campaign-context.json',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json'),Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')]:bind(p)
(O/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(O/'freeze-receipt.json').write_text(json.dumps({'status':'PASS','intake_exact_manifest':True,'direct_original_copy_bindings':True,'corpus_chunks_in_place':20,'inventory_frozen_inputs':8,'flat_references':len(refs),'recursive_expansion':False},indent=2)+'\n')
print('PASS',len(refs),'references; twenty chunks and eight frozen inputs')
