from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent;refs={}
def bind(p,h=None,s=None):
 p=p.resolve();b=p.read_bytes();v={'original':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 if h is not None: assert v['sha256']==h and (s is None or v['size']==s),str(p)
 refs[str(p)]=v
 return b
def manifest(d,allfiles=True):
 m=json.loads(bind(d/'manifest.json'))
 for e in (m['files'] if isinstance(m,dict) else m):
  if allfiles or e['path'].startswith('corpus/'):bind(d/e['path'],e['sha256'],e.get('size',e.get('bytes')))
 return m
A=L/'root-mathdb-breadth-intake-r427'
manifest(A)
for e in json.loads((A/'bindings.json').read_text()):bind(Path(e['original']),e['sha256'],e['size'])
I=L/'pi-mathdb-full-corpus-inventory-r301';m=manifest(I,False)
assert len([e for e in m['files'] if e['path'].startswith('corpus/')])==20
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:manifest(L/name)
for p in [Path('AGENTS.md'),Path('sources/upstream.json'),Path('sources/CONTENTS.md'),Path('sources/preprints-tree.json'),L.parent/'AGENTS.md',L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
(R/'bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(R/'preflight.json').write_text(json.dumps({'status':'PASS','r427_manifest_and_direct_originals':True,'r301_original_chunks':20,'r304_and_r363_manifests':True,'bindings':len(refs)},indent=2)+'\n')
print('PASS',len(refs)); print('coverage',len(json.loads((A/'coverage-delta.json').read_text())))
print('registry files',[(p.name,p.stat().st_size) for p in (L/'root-mathdb-accepted-exclusions-r304').glob('*.json')])
for e in (m['files'] if isinstance(m,dict) else m):
 if not e['path'].startswith('corpus/'):continue
 with (I/e['path']).open() as f:
  for line in f:
   o=json.loads(line)
   if str(o.get('mathdb_id',o.get('id')))=='395061': print(json.dumps(o,ensure_ascii=False));break
