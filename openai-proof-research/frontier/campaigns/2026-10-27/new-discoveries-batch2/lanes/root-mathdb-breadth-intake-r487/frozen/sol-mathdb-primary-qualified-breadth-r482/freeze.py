import json,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parent.parent; O=pathlib.Path(__file__).resolve().parent; I=L/'root-mathdb-circulant-13-prior-adjudication-r481'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def ref(p):return {'path':str(p),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def check(p,e):
 r=ref(p);assert r['sha256']==e['sha256'] and r['size']==e.get('size',e.get('bytes')),(p,r,e);return r
refs=[]
m=load(I/'manifest.json'); print('intake keys',m.keys())
for e in m['files']:refs.append(check(I/e['path'],e))
actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()};declared={e['path'] for e in m['files']};print('intake extras',actual-declared)
assert actual-declared=={'manifest.json','verification-receipt.json'}
refs.append(ref(I/'manifest.json'))
b=load(I/'bindings.json'); print('bindings type',type(b),str(b)[:1600])
cm=load(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];print('corpus entries',len(chunks),[e['path'] for e in chunks][:3])
for e in chunks+cm['frozen_inputs']:refs.append(check(C/e['path'],e))
refs.append(ref(C/'manifest.json'))
# Freeze flat input references before any statement/history reading. No recursive manifest traversal.
for name in ['accepted-exclusions.json','historical-dispositions.json']:refs.append(ref(L/'root-mathdb-accepted-exclusions-r304'/name))
for p in (L/'root-mathdb-cayley-review-intake-r363').iterdir():
 if p.is_file():refs.append(ref(p))
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:refs.append(ref(p))
(O/'flat-bindings.json').write_text(json.dumps(refs,indent=2))
print('queue structure',str(load(I/'queue.json'))[:1800]);print('reservation',load(I/'reserved-ids.json'));print('cm keys',cm.keys())
for e in b:
 for k in ['original','copy']:refs.append(check(pathlib.Path(e[k]),e))
for p in [I/'DECISION.md',I/'adjudications.json',I/'coverage-delta.json',L/'root-mathdb-accepted-exclusions-r304'/'accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304'/'historical-dispositions.json']+list((L/'root-mathdb-cayley-review-intake-r363').glob('*.json')):
 dest=O/'frozen'/p.parent.name/p.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes());refs.append(ref(p));refs.append(ref(dest))
(O/'flat-bindings.json').write_text(json.dumps(refs,indent=2))
(O/'freeze-receipt.json').write_text(json.dumps({'intake_exact':True,'direct_bindings':len(b),'chunks':len(chunks),'frozen_inputs':len(cm['frozen_inputs']),'scientific_reading_started':False},indent=2))
