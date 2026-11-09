import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r719';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 x=entry(p);assert x['sha256']==e['sha256'] and x['size']==e.get('size',e.get('bytes')),str(p)
refs={}
def bind(p):refs[str(p)]=entry(p)
for n in ['manifest.json','verification-receipt.json']:bind(I/n)
m=j(I/'manifest.json');names={e['path'] for e in m['files']}
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
for e in m['files']:check(I/e['path'],e);bind(I/e['path'])
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e);bind(pathlib.Path(e[k]))
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);bind(C/e['path'])
# Flat references only, not recursive history expansion.
for e in j(L/'sol-mathdb-primary-qualified-breadth-r716/flat-bindings.json'):check(pathlib.Path(e['path']),e);bind(pathlib.Path(e['path']))
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',*L.glob('*r304/accepted-exclusions.json'),*L.glob('*r304/historical-dispositions.json'),*L.glob('*r363/*DECISION*')]:
 if p.is_file():bind(p)
cov=j(I/'coverage-delta.json');assert len(cov)==8883
active=j(I/'active-breadth-reservations.json');seen=set()
for a in active:
 s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(a['protected_ids']);seen|=s
assert len(seen)==150
res=j(I/'reserved-ids-r720.json');q=j(I/'queue-r720.json');assert {r['mathdb_id'] for r in q}==set(res['ids']) and len(q)==50
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'initial-checks.json').write_text(json.dumps({'intake_exact':True,'direct_pairs':len(j(I/'bindings.json')),'chunks':20,'frozen_inputs':8,'coverage':8883,'reservations':150,'disjoint':True,'flat_references':len(refs)},indent=2)+'\n')
print((P/'initial-checks.json').read_text());print('queue metadata schema',list(q[0]));print('context references',[p for p in refs if any(x in p for x in ['r304/','r363/','ledger.json','prior-campaign-context'])])
