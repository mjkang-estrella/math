import json,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parent.parent; D=pathlib.Path(__file__).resolve().parent; I=L/'root-mathdb-breadth-intake-r649'
def meta(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
rows={}
def bind(p,h=None,n=None):
 p=pathlib.Path(p);r=meta(p)
 if h: assert r['sha256']==h,str(p)
 if n is not None: assert r['size']==n,str(p)
 rows[str(p)]=r
bind(I/'manifest.json','4671db8c05084f8dbe2865c1cb54615f15ab38f23edceda8c067c1d354f9c6ee',11223)
m=json.loads((I/'manifest.json').read_text()); expected={r['path'] for r in m['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected|{'manifest.json','verification-receipt.json'}
for r in m['files']:bind(I/r['path'],r['sha256'],r['size'])
bind(I/'verification-receipt.json','0a81e09ea66c1367b3387fe4c2b1ef38b0c2687e5a755855cc0ede8ac006c909',2392)
for r in json.loads((I/'bindings.json').read_text()):
 for k in ['original','copy']:bind(r[k],r['sha256'],r['bytes'])
inv=L/'pi-mathdb-full-corpus-inventory-r301/manifest.json'
x=json.loads(inv.read_text());print('INVENTORY',json.dumps(x)[:7000])
(D/'initial-bindings.json').write_text(json.dumps(list(rows.values()),indent=2)+'\n')
print('BOUND',len(rows))
chunks=[r for r in x['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(x['frozen_inputs'])==8
for r in chunks+x['frozen_inputs']:bind(inv.parent/r['path'],r['sha256'],r['bytes'])
for f in ['accepted-exclusions.json','historical-dispositions.json']:
 r=next(r for r in x['frozen_inputs'] if r['path']=='frozen/'+f);bind(L/'root-mathdb-accepted-exclusions-r304'/f,r['sha256'],r['bytes'])
for p in [L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L.parents[4]/'sources/upstream.json',L.parents[4]/'sources/CONTENTS.md']:
 if p.exists():bind(p)
(D/'flat-bindings.json').write_text(json.dumps(list(rows.values()),indent=2)+'\n')
print('CORPUS AND INPUTS BOUND',len(rows))
