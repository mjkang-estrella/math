import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r561';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def rec(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 r=rec(p);assert r['size']==e.get('size',e.get('bytes')) and r['sha256']==e['sha256'],str(p);return r
flat={}
def bind(p,e=None):
 r=check(p,e) if e else rec(p);flat[str(p)]=r
bind(I/'manifest.json',{'size':10593,'sha256':'92a14f8ea8bb6f488dde4e6c692abcf8d3ec2dc922da7a7fdb30ea29cc6233c6'})
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:bind(I/e['path'],e)
bind(I/'verification-receipt.json',{'size':446,'sha256':'0bc2c3ef8a92c73df076d95a4a2770ca65a8566dffcfa0c6a57b392a0905a4d6'})
for e in j(I/'bindings.json'):
 for k in ('original','copy'):bind(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363'/'DECISION.md']+list(L.glob('*r304/accepted-exclusions.json'))+list(L.glob('*r304/historical-dispositions.json')):bind(p)
(P/'flat-bindings.json').write_text(json.dumps(list(flat.values()),indent=2)+'\n')
print('BOUND',len(flat),'20 chunks 8 inputs; intake pairs verified; no upstream execution')
