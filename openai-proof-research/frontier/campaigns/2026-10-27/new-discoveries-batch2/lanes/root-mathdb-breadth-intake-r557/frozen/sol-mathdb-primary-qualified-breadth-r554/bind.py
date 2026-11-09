import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent; L=P.parent; I=L/'root-mathdb-breadth-intake-r553'
def info(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
refs={}
def bind(p,e=None):
 p=pathlib.Path(p); a=info(p)
 if e: assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p)
 refs[str(p)]=a
bind(I/'manifest.json');m=json.loads((I/'manifest.json').read_text())
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:bind(I/e['path'],e)
bind(I/'verification-receipt.json')
for e in json.loads((I/'bindings.json').read_text()):
 bind(e['original'],e);bind(e['copy'],e)
R=L/'pi-mathdb-full-corpus-inventory-r301';bind(R/'manifest.json',refs[str(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json')])
rm=json.loads((R/'manifest.json').read_text())
for e in rm['files']:
 if e['path'].startswith('corpus/'):bind(R/e['path'],e)
for e in rm['frozen_inputs']: 
 print('FROZEN_SCHEMA',e) if False else None
 p=e.get('path',e.get('original'));bind(p if pathlib.Path(p).is_absolute() else R/p,e)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
print('VERIFIED',len(refs),'flat references; chunks',sum(e['path'].startswith('corpus/') for e in rm['files']),'frozen',len(rm['frozen_inputs']))
for n in ['queue.json','reserved-ids.json','active-breadth-reservations.json','coverage-delta.json']:
 x=json.loads((I/n).read_text()); print(n,str(x)[:2600])
