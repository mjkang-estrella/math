import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r689';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def info(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
refs={}
def bind(p,e=None):
 a=info(p)
 if e:assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
 refs[str(p)]=a
bind(I/'manifest.json');bind(I/'verification-receipt.json')
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:bind(I/e['path'],e)
for e in j(I/'bindings.json'):
 for k in ['original','copy']:bind(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 bind(p)
# Bind only the named r363 decision, no historical recursion.
for p in (L/'root-cayley-hamilton-decision-r363').glob('*'):
 if p.is_file():bind(p)
active=j(I/'active-breadth-reservations.json');cov=j(I/'coverage-delta.json');assert len(cov)==8133
seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
assert len(seen)==150
q=j(I/'queue-r690.json');res=j(I/'reserved-ids-r690.json');assert len(q)==50 and {x['mathdb_id'] for x in q}==set(res['ids'])
bind(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'initial-checks.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_chunks':20,'frozen_inputs':8,'direct_pairs':len(j(I/'bindings.json')),'intake_exact':True,'disjoint_reservations':150,'baseline':8133,'prebinding_deviation':'Intake verification receipt and metadata queue prefix displayed before binding; no scientific statement read. Receipt subsequently independently bound; upstream verifier read but never executed.'},indent=2)+'\n')
print('PASS 20 chunks,8 frozen inputs,49 direct pairs, exact intake,150 disjoint reservations; bindings',len(refs))
