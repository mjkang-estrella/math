import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent.parent; O=pathlib.Path(__file__).resolve().parent; I=L/'root-mathdb-breadth-intake-r667'
def load(p):return json.loads(p.read_text())
def bind(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
def check(p,e):
 a=bind(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),(str(p),a,e);return a
refs=[bind(I/'manifest.json'),bind(I/'verification-receipt.json')]
m=load(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:refs.append(check(I/e['path'],e))
for e in load(I/'bindings.json'):
 for k in ['original','copy']:refs.append(check(pathlib.Path(e[k]),e))
R=L/'pi-mathdb-full-corpus-inventory-r301'; im=load(R/'manifest.json');chunks=[e for e in im['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:refs.append(check(R/e['path'],e))
print('inventory keys',im.keys());print('frozen inputs',json.dumps(im.get('frozen_inputs'),indent=2))
for e in im['frozen_inputs']:
 p=pathlib.Path(e['path']);p=p if p.is_absolute() else R/p
 refs.append(check(p,e))
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-breadth-intake-r304'/'accepted-exclusions.json',L/'root-mathdb-breadth-intake-r304'/'historical-dispositions.json']:
 if p.exists():refs.append(bind(p))
(O/'initial-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
print('BOUND',len(refs),'20 chunks and',len(im['frozen_inputs']),'inputs')
