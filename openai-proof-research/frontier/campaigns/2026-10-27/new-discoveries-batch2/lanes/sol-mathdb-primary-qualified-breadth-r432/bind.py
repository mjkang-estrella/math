import json,hashlib,pathlib
R=pathlib.Path.cwd();L=R/'frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes';O=L/'sol-mathdb-primary-qualified-breadth-r432';I=L/'root-mathdb-breadth-intake-r431'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
bound={}
def bind(p,sha=None,size=None,role='original'):
 p=p.resolve(); d=digest(p);n=p.stat().st_size
 assert sha is None or sha==d,(str(p),'hash')
 assert size is None or size==n,(str(p),'size')
 bound[str(p)]={'original':str(p),'sha256':d,'size':n,'role':role}
bind(I/'manifest.json',role='r431 manifest')
for e in load(I/'manifest.json')['files']:bind(I/e['path'],e['sha256'],e['size'],'r431 manifest payload')
for e in load(I/'bindings.json'):bind(pathlib.Path(e['original']),e['sha256'],e['size'],'r431 direct original')
bind(C/'manifest.json',role='r301 manifest')
chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
assert len(chunks)==20
for e in chunks:bind(C/e['path'],e['sha256'],e['bytes'],'r301 original corpus chunk')
for pat,names in [('*r304',['manifest.json','accepted-exclusions.json','historical-dispositions.json']),('*r363',['manifest.json','disposition.json','coverage-delta.json','reserved-ids.json'])]:
 p=next(L.glob(pat));m=load(p/'manifest.json'); entries={e['path']:e for e in (m['files'] if isinstance(m,dict) else m)}
 for name in names:
  e=entries.get(name);bind(p/name,e['sha256'] if e else None,(e.get('size',e.get('bytes'))) if e else None,pat+' administrative original')
for name in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json']:
 bind(R/name,role='administrative original')
(O/'bindings.json').write_text(json.dumps(list(bound.values()),indent=2)+'\n')
(O/'preflight.json').write_text(json.dumps({'status':'PASS','direct_flat_bindings':len(bound),'original_chunks':20,'upstream_verifiers_run':False},indent=2)+'\n')
print('BOUND',len(bound),'CHUNKS',len(chunks))
