import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r615';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def ent(p):
 b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):assert ent(p)=={'sha256':e['sha256'],'size':e.get('size',e.get('bytes'))},str(p)
b={}
def bind(p):b[str(p)]=ent(p)
assert ent(I/'manifest.json')=={'sha256':'d3ded06c6a20fe4acefd4c63a1835a25c891707605d1c8e8a3d79c6a43f209fe','size':10492}
bind(I/'manifest.json');m=j(I/'manifest.json')
assert {str(x.relative_to(I)) for x in I.rglob('*') if x.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:check(I/e['path'],e);bind(I/e['path'])
bind(I/'verification-receipt.json')
for e in j(I/'bindings.json'):
 for k in ['original','copy']:p=pathlib.Path(e[k]);check(p,e);bind(p)
# One flat bound reference table; no historical tree traversal.
f=L/'sol-mathdb-primary-qualified-breadth-r612/flat-bindings.json';bind(f)
for path,e in j(f).items():p=pathlib.Path(path);check(p,e);bind(p)
check(C/'manifest.json',ent(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'));bind(C/'manifest.json');cm=j(C/'manifest.json')
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:p=C/e['path'];check(p,e);bind(p)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 bind(p)
for p in L.glob('*r363*/*'):
 if p.is_file():bind(p)
(P/'flat-bindings.json').write_text(json.dumps(b,indent=2,sort_keys=True)+'\n')
(P/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files_bound':len(b),'original_chunks':20,'frozen_inputs':8,'intake_exact_payload':True,'direct_pairs':True,'intake_manifest':ent(I/'manifest.json')},indent=2)+'\n')
print('BOUND',len(b))
for name in ['active-breadth-reservations.json','reserved-ids-r616.json','coverage-delta.json']:
 d=j(I/name);print(name,str(d)[:2200])
print('chunk sample',next(iter((C/'corpus/mathdb-normalized-chunk-0001.jsonl').open()))[:2200])
