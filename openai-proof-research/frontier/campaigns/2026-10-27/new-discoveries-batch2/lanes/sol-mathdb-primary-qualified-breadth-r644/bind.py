import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r643'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,x):
 a=entry(p);assert a['size']==x.get('size',x.get('bytes')) and a['sha256']==x['sha256'],str(p);return a
bindings={}
def bind(p,x=None):
 p=pathlib.Path(p);a=check(p,x) if x else entry(p);bindings[str(p)]=a;return a
bind(I/'manifest.json',dict(size=19288,sha256='b6da03bcc5fe26301219dcc65cc4072b25f4592356bcb142f3bed681ecc19447'))
m=load(I/'manifest.json'); expected={x['path'] for x in m['files']};actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert actual==expected
for x in m['files']:bind(I/x['path'],x)
bind(I/'verification-receipt.json')
for x in load(I/'bindings.json'):
 bind(x['original'],x);bind(x['copy'],x);assert pathlib.Path(x['original']).read_bytes()==pathlib.Path(x['copy']).read_bytes()
bind(R/'manifest.json',next(x for x in m['files'] if x['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'))
r=load(R/'manifest.json');print('r301 frozen schema',str(r.get('frozen_inputs'))[:4000])
chunks=[x for x in r['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20
for x in chunks:bind(R/x['path'],x)
for x in r.get('frozen_inputs',[]):
 print('frozen',x);bind(R/x['path'],x)
# Flat historical references, no recursive history expansion.
f=load(L/'sol-mathdb-primary-qualified-breadth-r642/flat-bindings.json');print('flat schema',str(f)[:700])
(P/'initial-bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
print('bound',len(bindings))
