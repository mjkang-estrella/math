import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parent.parent; O=pathlib.Path(__file__).resolve().parent; I=L/'root-mathdb-breadth-intake-r687'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def sig(p):
 h=hashlib.sha256();n=0
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b);n+=len(b)
 return {'sha256':h.hexdigest(),'size':n}
def load(p):return json.loads(p.read_text())
refs={}
def bind(p,expect=None):
 s=sig(p)
 if expect:assert s=={'sha256':expect['sha256'],'size':expect.get('size',expect.get('bytes'))},str(p)
 refs[str(p)]=dict(path=str(p),**s)
bind(I/'manifest.json');m=load(I/'manifest.json')
assert set(str(p.relative_to(I)) for p in I.rglob('*') if p.is_file())=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:bind(I/e['path'],e)
bind(I/'verification-receipt.json')
for e in load(I/'bindings.json'):
 bind(pathlib.Path(e['original']),e);bind(pathlib.Path(e['copy']),e)
 assert pathlib.Path(e['original']).read_bytes()==pathlib.Path(e['copy']).read_bytes()
bind(R/'manifest.json',next(e for e in m['files'] if e['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'))
rm=load(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for e in chunks+rm['frozen_inputs']:bind(R/e['path'],e)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 if p.exists():bind(p)
# Bind decision/exclusion references without reading content.
for pattern in ['*r363*/*DECISION*','root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 for p in L.glob(pattern):
  if p.is_file():bind(p)
(O/'initial-bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':list(refs.values()),'chunks':20,'frozen_inputs':8,'direct_pairs':len(load(I/'bindings.json'))},indent=2)+'\n')
print('PASS intake exact payload; all direct pairs; 20 original chunks and 8 frozen inputs; bindings',len(refs))
