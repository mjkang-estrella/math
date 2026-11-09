import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r543'
def stamp(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
bound={}
def bind(p):
 s=stamp(p);bound[str(p)]=s;return s
def check(p,e):
 s=bind(p);assert s['sha256']==e['sha256'] and s['size']==e.get('size',e.get('bytes')),(p,s,e)
for p in I.iterdir():
 if p.is_file():bind(p)
m=json.loads((I/'manifest.json').read_text());expected={e['path'] for e in m['files']}
actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}
assert actual==expected|set(m['excluded_exact_paths'])
for e in m['files']:check(I/e['path'],e)
for e in json.loads((I/'bindings.json').read_text()):
 check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
R=L/'pi-mathdb-full-corpus-inventory-r301'; rm=json.loads((R/'manifest.json').read_text())
print('inventory keys',rm.keys())
for k in ['corpus_chunks','frozen_inputs','files']:
 if k in rm:print(k,str(rm[k])[:4000])
(D/'flat-bindings.json').write_text(json.dumps(list(bound.values()),indent=2)+'\n')
print('Initial bindings',len(bound))
chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
for p in [L/'root-mathdb-accepted-exclusions-r304'/'accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304'/'historical-dispositions.json']:
 e=next(x for x in rm['frozen_inputs'] if x['path']=='frozen/'+p.name);check(p,e)
for folder in L.glob('*r363'):
 for p in folder.iterdir():
  if p.is_file():bind(p)
B=D.parent.parent
for p in [B/'ledger.json',B/'prior-campaign-context.json']:
 if p.exists():bind(p)
(D/'flat-bindings.json').write_text(json.dumps(list(bound.values()),indent=2)+'\n')
print('All bound',len(bound),'chunks',len(chunks),'frozen',len(rm['frozen_inputs']))
