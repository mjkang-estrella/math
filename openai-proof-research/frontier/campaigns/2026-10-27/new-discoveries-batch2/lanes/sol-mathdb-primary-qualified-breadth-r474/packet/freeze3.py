import json,hashlib,pathlib,datetime
B=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'); L=B/'lanes'; O=L/'sol-mathdb-primary-qualified-breadth-r474'
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
refs={}
def bind(p):
 p=p.resolve(); refs[str(p)]={'path':str(p),'bytes':p.stat().st_size,'sha256':digest(p)}
for name in ['root-mathdb-breadth-intake-r473','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/name; m=json.loads((d/'manifest.json').read_text());bind(d/'manifest.json')
 for e in (m if isinstance(m,list) else m['files']+m.get('frozen_inputs',[])):
  p=d/e['path'];bind(p);assert refs[str(p.resolve())]['sha256']==e['sha256'],str(p)
  assert e.get('size',e.get('bytes',p.stat().st_size))==p.stat().st_size,str(p)
 print(name,'manifest validated')
 if name=='pi-mathdb-full-corpus-inventory-r301':
  print('FROZEN',json.dumps(m.get('frozen_inputs')))
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md',B.parents[3]/'sources/upstream.json',B.parents[3]/'sources/CONTENTS.md',B.parents[3]/'sources/preprints-tree.json']:
 if p.exists():bind(p)
# Bind direct original paths named by intake bindings without recursive traversal.
b=json.loads((L/'root-mathdb-breadth-intake-r473/bindings.json').read_text())
for e in b:
 p=pathlib.Path(e['original']);bind(p);assert digest(p)==e['sha256'];assert p.stat().st_size==e['size']
(O/'bindings.json').write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'flat_refs':list(refs.values())},indent=2)+'\n')
print('PASS frozen',len(refs))
