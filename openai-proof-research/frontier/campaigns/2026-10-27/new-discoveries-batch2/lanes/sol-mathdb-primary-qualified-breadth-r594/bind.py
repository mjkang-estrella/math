import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r593';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=entry(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p)
refs={}
def bind(p):refs[str(p)]=entry(p)
for n in ['manifest.json','bindings.json','queue.json','reserved-ids.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','active-breadth-reservations.json']:bind(I/n)
assert refs[str(I/'manifest.json')]['sha256']=='c0e47e4e35ab9e7f4febfcb62cd1626c1ffe92e843549b95494c7a88012fb8f2'
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:check(I/e['path'],e);bind(I/e['path'])
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e);bind(pathlib.Path(e[k]))
cm=j(C/'manifest.json');bind(C/'manifest.json');assert entry(C/'manifest.json')['sha256']=='4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15'
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);bind(C/e['path'])
for f in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 if f.exists():bind(f)
for lane,ns in [('pi-mathdb-disjoint-intake-r304',['accepted-exclusions.json','historical-dispositions.json'])]:
 for n in ns:
  for f in L.glob('*/'+n):bind(f)
for f in L.glob('*r363/*'):
 if f.is_file():bind(f)
# Bind parked-route evidence before reading any scientific/admin context.
for pat in ['*r578/*','*r542/*']:
 for f in L.glob(pat):
  if f.is_file():bind(f)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'binding-receipt.json').write_text(json.dumps({'intake_exact':True,'direct_original_copy_pairs':len(j(I/'bindings.json')),'original_chunks':len(chunks),'original_frozen_inputs':8,'references':len(refs)},indent=2)+'\n')
print((P/'binding-receipt.json').read_text())
