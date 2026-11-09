import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r715';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=entry(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
def write(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
refs={}
def bind(p):refs[str(p)]=entry(p)
for n in ['manifest.json','queue-r716.json','reserved-ids-r716.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','bindings.json','active-breadth-reservations.json']:bind(I/n)
m=j(I/'manifest.json');names={e['path'] for e in m['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
for e in m['files']:check(I/e['path'],e);bind(I/e['path'])
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e);bind(pathlib.Path(e[k]))
cm=j(C/'manifest.json');assert (C/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes();bind(C/'manifest.json')
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);bind(C/e['path'])
# Flat references only; no historical recursive expansion.
for e in j(L/'sol-mathdb-primary-qualified-breadth-r712/flat-bindings.json'):check(pathlib.Path(e['path']),e);bind(pathlib.Path(e['path']))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-cayley-acceptance-decision-r363/DECISION.md']:
 if p.exists():bind(p)
cov=j(I/'coverage-delta.json');assert len(cov)==8783
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
assert len(active)==3 and len(seen)==150
q=j(I/'queue-r716.json');res=j(I/'reserved-ids-r716.json');assert len(q)==50 and {r['mathdb_id'] for r in q}==set(res['ids'])
write('flat-bindings.json',list(refs.values()));write('initial-checks.json',{'intake_exact':True,'original_copy_pairs':len(j(I/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'coverage_baseline':len(cov),'reservations':150,'disjoint':True,'scientific_reading_started':False})
print('PASS',len(refs),'flat bindings;20 chunks;8 inputs;150 disjoint reservations')
