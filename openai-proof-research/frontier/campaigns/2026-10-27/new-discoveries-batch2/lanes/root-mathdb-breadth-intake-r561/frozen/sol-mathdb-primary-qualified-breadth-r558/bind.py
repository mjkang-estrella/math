from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r557'
def h(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def save(n,x):(D/n).write_text(json.dumps(x,indent=2)+'\n')
m=json.loads((I/'manifest.json').read_bytes()); refs=[]
for e in m['files']:
 p=I/e['path']; a=h(p); assert a['size']==e['size'] and a['sha256']==e['sha256'];refs.append(a)
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|{'manifest.json','verification-receipt.json'}
for e in json.loads((I/'bindings.json').read_bytes()):
 for k in ['original','copy']:
  a=h(Path(e[k]));assert a['size']==e['size'] and a['sha256']==e['sha256'];refs.append(a)
# Original inventory manifest is now bound and matched to frozen copy.
R=L/'pi-mathdb-full-corpus-inventory-r301'; rm=json.loads((R/'manifest.json').read_bytes())
print('manifest keys',rm.keys())
for e in rm['files']:
 if e['path'].startswith('corpus/'):
  a=h(R/e['path']);assert a['size']==e.get('bytes',e.get('size')) and a['sha256']==e['sha256'];refs.append(a)
print('frozen inputs',rm.get('frozen_inputs'))
for e in rm.get('frozen_inputs',[]):
 p=Path(e.get('path',e.get('file','')));p=p if p.is_absolute() else R/p
 a=h(p);assert a['size']==e.get('bytes',e.get('size')) and a['sha256']==e['sha256'];refs.append(a)
for p in [I/'manifest.json',I/'verification-receipt.json',L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'pi-mathdb-primary-qualified-breadth-r304/accepted-exclusions.json',L/'pi-mathdb-primary-qualified-breadth-r304/historical-dispositions.json']:
 if p.exists(): refs.append(h(p))
save('flat-bindings.json',list({x['path']:x for x in refs}.values()))
print('bindings',len(refs),'chunks',sum(e['path'].startswith('corpus/') for e in rm['files']))
