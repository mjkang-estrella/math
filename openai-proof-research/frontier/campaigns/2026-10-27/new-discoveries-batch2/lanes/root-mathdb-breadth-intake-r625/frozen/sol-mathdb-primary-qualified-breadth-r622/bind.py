import json,hashlib,pathlib
P=pathlib.Path(__file__).resolve().parent; L=P.parent; I=L/'root-mathdb-breadth-intake-r621'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def h(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def load(p):return json.loads(p.read_text())
refs={}
def check(p,d):
 a=h(p);assert a['sha256']==d['sha256'] and a['size']==d.get('size',d.get('bytes')),str(p);refs[str(p)]=a
assert h(I/'manifest.json')['sha256']=='69a8ab79efe4eea65f8084c743c0862ee430985e81bec1577930e77ba738e3f3'
refs[str(I/'manifest.json')]=h(I/'manifest.json')
m=load(I/'manifest.json');assert {str(x.relative_to(I)) for x in I.rglob('*') if x.is_file()}=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
for d in m['files']:check(I/d['path'],d)
refs[str(I/'verification-receipt.json')]=h(I/'verification-receipt.json')
for d in load(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(d[k]),d)
cm=load(C/'manifest.json');print('inventory keys',cm.keys());print('frozen',cm.get('frozen_inputs'))
chunks=[d for d in cm['files'] if d['path'].startswith('corpus/')];assert len(chunks)==20
for d in chunks:check(C/d['path'],d)
for d in cm['frozen_inputs']:check(pathlib.Path(d['path']) if pathlib.Path(d['path']).is_absolute() else C/d['path'],d)
for name in ['ledger.json','prior-campaign-context.json']:
 p=L.parent/name;refs[str(p)]=h(p)
for pat in ['*r304/accepted-exclusions.json','*r304/historical-dispositions.json','*r363/*']:
 for p in L.glob(pat):
  if p.is_file():refs[str(p)]=h(p)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'binding-receipt.json').write_text(json.dumps({'intake_exact_payload':True,'original_copy_pairs':len(load(I/'bindings.json')),'original_chunks':len(chunks),'frozen_inputs':len(cm['frozen_inputs'])},indent=2)+'\n')
print('bound',len(refs))
