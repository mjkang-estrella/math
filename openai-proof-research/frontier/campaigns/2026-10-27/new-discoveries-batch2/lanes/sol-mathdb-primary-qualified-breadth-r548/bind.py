import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent; L=P.parent; I=L/'root-mathdb-breadth-intake-r547'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=entry(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
refs={}
def bind(p):refs[str(p)]=entry(p)
for p in I.rglob('*'):
 if p.is_file():bind(p)
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:check(I/e['path'],e)
for e in j(I/'bindings.json'):
 for k in ['original','copy']:
  p=pathlib.Path(e[k]);check(p,e);bind(p)
cm=j(C/'manifest.json');check(C/'manifest.json',next(e for e in j(I/'bindings.json') if e['original']==str(C/'manifest.json')))
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);bind(C/e['path'])
for rel in ['ledger.json','prior-campaign-context.json','lanes/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','lanes/root-mathdb-accepted-exclusions-r304/historical-dispositions.json','lanes/root-mathdb-cayley-review-intake-r363/DECISION.md']:
 bind(L.parent/rel)
res=j(I/'reserved-ids.json');q=j(I/'queue.json');cov=j(I/'coverage-delta.json');assert len(cov)==4633;assert {r['mathdb_id'] for r in q}==set(res['ids']) and len(q)==50
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
assert len(seen)==150
for r in j(I/'active-breadth-reservations.json'):assert set(r['other_active_reservations'])==seen-set(r['ids'])
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact':True,'original_copy_pairs':len(j(I/'bindings.json')),'chunks':20,'frozen_inputs':8,'coverage':4633,'reserved_total':150,'manifest':entry(I/'manifest.json')},indent=2)+'\n')
print('BIND PASS',len(refs))
