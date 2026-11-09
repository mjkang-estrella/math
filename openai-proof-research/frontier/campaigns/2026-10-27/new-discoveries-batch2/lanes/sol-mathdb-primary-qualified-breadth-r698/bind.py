import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r697';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 a=entry(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p)
refs={}
def bind(p):refs[str(p)]=entry(p)
for p in [I/'manifest.json',I/'verification-receipt.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
m=j(I/'manifest.json');names={e['path'] for e in m['files']}
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
for e in m['files']:check(I/e['path'],e);bind(I/e['path'])
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e);bind(pathlib.Path(e[k]))
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);bind(C/e['path'])
# Bind flat references, without opening their scientific/admin content.
for e in j(L/'sol-mathdb-primary-qualified-breadth-r694/flat-bindings.json'):
 p=pathlib.Path(e['path']);check(p,e);bind(p)
for name in ['ledger.json','prior-campaign-context.json']:
 bind(L.parent/name)
for p in L.glob('*r304/accepted-exclusions.json'):bind(p)
for p in L.glob('*r304/historical-dispositions.json'):bind(p)
for p in L.glob('*r363/*'):
 if p.is_file():bind(p)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'initial-checks.json').write_text(json.dumps({'intake_exact':True,'direct_original_copy_pairs':len(j(I/'bindings.json')),'corpus_chunks_in_place':20,'separate_frozen_inputs':8,'bound_references':len(refs)},indent=2)+'\n')
print((P/'initial-checks.json').read_text())
for n in ['queue-r698.json','reserved-ids-r698.json','active-breadth-reservations.json']:
 a=j(I/n);print(n, type(a).__name__,list(a[0] if isinstance(a,list) else a)[:12])
print('chunk schema',list(json.loads((C/chunks[0]['path']).open().readline())))
