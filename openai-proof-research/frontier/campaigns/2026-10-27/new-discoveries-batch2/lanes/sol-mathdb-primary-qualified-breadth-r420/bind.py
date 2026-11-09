from pathlib import Path
import json,hashlib
W=Path(__file__).resolve().parent; L=W.parent; bindings={}
def digest(p):
 b=p.read_bytes(); return {'original':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def bind(p,expected=None):
 d=digest(p)
 if expected:
  assert d['sha256']==expected['sha256'] and d['size']==expected.get('size',expected.get('bytes',d['size'])),str(p)
 bindings[str(p)]=d
 return d
def manifest(name,allfiles=True):
 p=L/name/'manifest.json';bind(p);m=json.loads(p.read_text())
 for e in m['files']:
  if allfiles or e['path'].startswith('corpus/'):
   bind(p.parent/e['path'],e)
 return m
m=manifest('root-mathdb-breadth-intake-r419')
for e in json.loads((L/'root-mathdb-breadth-intake-r419/bindings.json').read_text()):bind(Path(e['original']),e)
m=manifest('pi-mathdb-full-corpus-inventory-r301',False)
assert sum(e['path'].startswith('corpus/') for e in m['files'])==20
for name,files in [('root-mathdb-accepted-exclusions-r304',['accepted-exclusions.json','historical-dispositions.json','bindings.json']),('root-mathdb-cayley-review-intake-r363',['disposition.json','bindings.json'])]:
 p=L/name/'manifest.json';bind(p);mm=json.loads(p.read_text()); ee={e['path']:e for e in (mm['files'] if isinstance(mm,dict) else mm)}
 for f in files:bind(p.parent/f,ee[f])
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:bind(p)
(W/'bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
(W/'preflight.json').write_text(json.dumps({'ok':True,'bound_originals':len(bindings),'corpus_chunks':20,'r419_manifest_verified':True,'r419_bound_originals_verified':True,'r304_registries_bound':True,'r363_disposition_bound':True},indent=2)+'\n')
print('PASS',len(bindings),'originals bound before scientific reads')
