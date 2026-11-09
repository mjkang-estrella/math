import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r509'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=entry(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
def exact(p,m):
 assert {str(q.relative_to(p)) for q in p.rglob('*') if q.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
 for e in m['files']:check(p/e['path'],e)
refs={}
def bind(p):refs[str(p)]=entry(p)
for n in ['manifest.json','bindings.json','queue.json','reserved-ids.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','active-breadth-reservations.json']:bind(I/n)
exact(I,j(I/'manifest.json'))
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e);bind(pathlib.Path(e[k]))
N=I/'frozen/sol-mathdb-primary-qualified-breadth-r506'
for n in ['initial-bindings.json','flat-bindings.json','corpus-bindings.json','source-bindings.json','derivative-bindings.json']:
 for e in j(N/n):
  if 'path' in e:check(pathlib.Path(e['path']),e);bind(pathlib.Path(e['path']))
C=L/'pi-mathdb-full-corpus-inventory-r301';cm=j(C/'manifest.json');check(C/'manifest.json',entry(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json'));bind(C/'manifest.json')
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);bind(C/e['path'])
for n in ['ledger.json','prior-campaign-context.json']:bind(L.parent/n)
# Explicit required context paths: bind bytes before opening.
for p in [L/'root-mathdb-breadth-intake-r304/accepted-exclusions.json',L/'root-mathdb-breadth-intake-r304/historical-dispositions.json']:
 if p.exists():bind(p)
for p in L.glob('*r363/DECISION.md'):bind(p)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
res=j(I/'reserved-ids.json');cov=j(I/'coverage-delta.json');assert len(cov)==3783
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not {str(x) for x in ids}&set(cov) and not ids&set(r['protected_ids']);seen|=ids
assert len(seen)==150 and res['lane']==P.name and set(res['ids'])=={r['mathdb_id'] for r in j(I/'queue.json')}
(P/'initial-verification.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_intake':True,'direct_pairs':len(j(I/'bindings.json')),'chunks':20,'frozen_inputs':8,'flat_references':len(refs),'disjoint_reserved':150},indent=2)+'\n')
print('BOUND',len(refs));print('CONTEXT',*[x for x in refs if 'r304/' in x or 'r363/' in x],sep='\n')
print('manifest schema',list(cm));print('coverage schema',list(cov)[:2])
