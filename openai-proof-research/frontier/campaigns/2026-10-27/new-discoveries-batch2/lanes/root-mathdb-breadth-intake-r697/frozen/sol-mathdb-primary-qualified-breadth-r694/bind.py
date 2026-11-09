import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r693';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def binding(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 b=binding(p);assert b['sha256']==e['sha256'] and b['size']==e.get('size',e.get('bytes')),str(p)
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
bound={}
def bind(p):bound[str(p)]=binding(p)
for p in I.rglob('*'):
 if p.is_file():bind(p)
m=j(I/'manifest.json');names={e['path'] for e in m['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
for e in m['files']:check(I/e['path'],e)
for e in j(I/'bindings.json'):
 for k in ['original','copy']:p=pathlib.Path(e[k]);check(p,e);bind(p)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:p=C/e['path'];check(p,e);bind(p)
# Bind flat referenced files, but never expand historical trees.
for e in j(L/'sol-mathdb-primary-qualified-breadth-r690/flat-bindings.json'):
 p=pathlib.Path(e['path']);check(p,e);bind(p)
# Explicit required context, bound before reading.
for rel in ['ledger.json','prior-campaign-context.json']:
 p=L.parent/rel;bind(p)
for name in ['root-mathdb-full-corpus-router-r304/accepted-exclusions.json','root-mathdb-full-corpus-router-r304/historical-dispositions.json']:
 p=L/name
 if p.exists():bind(p)
# Locate only filenames for required context.
for p in L.glob('*r304/*.json'):
 if p.name in ['accepted-exclusions.json','historical-dispositions.json']:bind(p)
for p in L.glob('*r363/*'):
 if p.is_file() and p.name in ['DECISION.md','decision.json','SUMMARY.md']:bind(p)
write('flat-bindings.json',list(bound.values()))
write('initial-checks.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact_payload':True,'direct_pairs':len(j(I/'bindings.json')),'corpus_chunks':20,'frozen_inputs':8,'scientific_reading_started':False})
print('CHECKED',len(bound),'bindings;20 chunks;8 inputs; direct original/copy pairs',len(j(I/'bindings.json')))
print('CONTEXT',*[x for x in bound if any(s in x for s in ['r304/accepted','r304/historical','r363/','ledger.json','prior-campaign-context'])],sep='\n')
