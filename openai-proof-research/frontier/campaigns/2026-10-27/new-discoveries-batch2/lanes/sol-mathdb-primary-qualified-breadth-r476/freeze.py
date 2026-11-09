import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent; L=D.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bindings={}; checks=[]
def bind(p,expected=None,size=None):
 p=pathlib.Path(p).resolve(); digest=h(p); n=p.stat().st_size
 if expected: assert digest==expected,(str(p),digest,expected)
 if size is not None: assert n==size,(str(p),n,size)
 bindings[str(p)]={'path':str(p),'sha256':digest,'bytes':n}
def manifest(name,full=True):
 root=L/name; p=root/'manifest.json';bind(p);m=json.loads(p.read_text()); rows=m if isinstance(m,list) else m['files']
 for r in rows:bind(root/r['path'],r['sha256'],r.get('size',r.get('bytes')))
 checks.append({'manifest':str(p),'entries':len(rows),'pass':True})
 return m
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363','root-mathdb-breadth-intake-r475']:manifest(name)
I=L/'root-mathdb-breadth-intake-r475'
for r in json.loads((I/'bindings.json').read_text()):
 bind(r['original'],r['sha256'],r.get('size',r.get('bytes')))
 if r.get('copy'):bind(r['copy'],r['sha256'],r.get('size',r.get('bytes')))
V=L/'pi-mathdb-full-corpus-inventory-r301';bind(V/'manifest.json');m=json.loads((V/'manifest.json').read_text())
chunks=[r for r in m['files'] if r['path'].startswith('corpus/mathdb-normalized-chunk-')]; assert len(chunks)==20
assert len(m['frozen_inputs'])==8
for r in chunks+m['frozen_inputs']:bind(V/r['path'],r['sha256'],r['bytes'])
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:bind(L.parent/name)
R=L.parents[4]
for name in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md']:bind(R/name)
(D/'bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
(D/'freeze-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'bindings':len(bindings),'chunks':20,'frozen_inputs':8,'status':'PASS'},indent=2)+'\n')
print('PASS',len(bindings), 'flat bindings; 20 chunks and 8 explicit frozen inputs')
