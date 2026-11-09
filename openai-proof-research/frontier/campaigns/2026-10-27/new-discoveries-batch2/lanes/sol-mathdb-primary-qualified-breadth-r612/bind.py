import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r611';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def ent(p):
 b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 a=ent(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p)
def exact(p,m):
 assert {str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
 for e in m['files']:check(p/e['path'],e)
b={}
def bind(p):b[str(p)]=ent(p)
bind(I/'manifest.json');exact(I,j(I/'manifest.json'));bind(I/'verification-receipt.json')
for e in j(I/'manifest.json')['files']:bind(I/e['path'])
for e in j(I/'bindings.json'):
 for k in ['original','copy']:p=pathlib.Path(e[k]);check(p,e);bind(p)
# Flat original references: no historical directory expansion.
for lane in ['root-mathdb-breadth-intake-r609','sol-mathdb-primary-qualified-breadth-r606']:
 f=L/lane/('bindings.json' if lane.startswith('root') else 'flat-bindings.json');bind(f);data=j(f)
 if isinstance(data,list):
  for e in data:
   for k in ['original','copy']:p=pathlib.Path(e[k]);check(p,e);bind(p)
 else:
  for path,e in data.items():p=pathlib.Path(path);check(p,e);bind(p)
cm=j(C/'manifest.json');check(C/'manifest.json',ent(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'));bind(C/'manifest.json')
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:p=C/e['path'];check(p,e);bind(p)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-breadth-intake-r304/accepted-exclusions.json',L/'root-mathdb-breadth-intake-r304/historical-dispositions.json']:
 if p.exists():bind(p)
(P/'flat-bindings.json').write_text(json.dumps(b,indent=2,sort_keys=True)+'\n')
(P/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files_bound':len(b),'original_chunks':20,'frozen_inputs':8,'intake_exact_payload':True,'direct_pairs':True,'intake_manifest':ent(I/'manifest.json')},indent=2)+'\n')
print('BOUND',len(b));print('queue structure',str(j(I/'queue-r612.json'))[:2500]);print('reservations',str(j(I/'active-breadth-reservations.json'))[:1200]);print('corpus manifest keys',cm.keys())
