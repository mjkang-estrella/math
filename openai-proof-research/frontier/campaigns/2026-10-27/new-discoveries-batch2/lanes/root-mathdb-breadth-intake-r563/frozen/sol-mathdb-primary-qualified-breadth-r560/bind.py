import json,hashlib,pathlib
D=pathlib.Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r559'
def ent(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 a=ent(p);assert a['sha256']==e['sha256'] and a['size']==e.get('size',e.get('bytes')),str(p);return a
out=[ent(I/'manifest.json'),ent(I/'verification-receipt.json')]
m=json.loads((I/'manifest.json').read_text());assert set(str(p.relative_to(I)) for p in I.rglob('*') if p.is_file())==set(e['path'] for e in m['files'])|set(m['excluded_exact_paths'])
for e in m['files']:out.append(check(I/e['path'],e))
for e in json.loads((I/'bindings.json').read_text()):
 for k in ['original','copy']:out.append(check(pathlib.Path(e[k]),e))
r=L/'pi-mathdb-full-corpus-inventory-r301'; rm=json.loads((r/'manifest.json').read_text());print('inventory keys',rm.keys())
for e in rm['files']:
 if e['path'].startswith('corpus/'):out.append(check(r/e['path'],e))
print('frozen_inputs',rm.get('frozen_inputs'))
for e in rm.get('frozen_inputs',[]):
 p=pathlib.Path(e.get('path',e.get('original','')));p=p if p.is_absolute() else r/p;out.append(check(p,e))
# Bind required context and helper before content inspection.
for p in [L/'root-mathdb-breadth-intake-r304'/'accepted-exclusions.json',L/'root-mathdb-breadth-intake-r304'/'historical-dispositions.json']:
 if p.exists():out.append(ent(p))
for p in L.glob('*r363*/*'):
 if p.is_file():out.append(ent(p))
for p in [D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 if p.exists():out.append(ent(p))
(D/'flat-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print('bound',len(out),'chunks',sum('/corpus/' in a['path'] for a in out))
