import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r571';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def ent(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=ent(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
b={}
def bind(p):b[str(p)]=ent(p)
bind(I/'manifest.json');assert b[str(I/'manifest.json')]['sha256']=='673835750099e45707372f880d12662ce9cc7ec2fc423863c262b819d55821fc'
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:check(I/e['path'],e);bind(I/e['path'])
bind(I/'verification-receipt.json')
for e in j(I/'bindings.json'):
 for k in ('original','copy'):check(pathlib.Path(e[k]),e);bind(pathlib.Path(e[k]))
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);bind(C/e['path'])
for e in j(L/'sol-mathdb-primary-qualified-breadth-r568/flat-bindings.json'):check(pathlib.Path(e['path']),e);bind(pathlib.Path(e['path']))
for lane in ['root-mathdb-breadth-intake-r304','root-mathdb-breadth-intake-r363']:
 for name in ['accepted-exclusions.json','historical-dispositions.json','DECISION.md']:
  p=L/lane/name
  if p.exists():bind(p)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
(P/'flat-bindings.json').write_text(json.dumps(list(b.values()),indent=2)+'\n')
(P/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':len(b),'chunks':20,'frozen_inputs':8,'upstream_verify_executed':False,'deviation':'Before durable binding, shell output exposed first 3 queue titles and upstream verify.py/manifest structural headers; no dispositions made then. Hashes were obtained first for intake JSON; all payloads independently verified before statement review.'},indent=2)+'\n')
print('BOUND',len(b))
