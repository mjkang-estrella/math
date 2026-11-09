import json,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parent; I=L.parent/'root-mathdb-breadth-intake-r685'
def bind(p):
 b=p.read_bytes(); return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,h,s):
 r=bind(p);assert r['sha256']==h and r['size']==s,str(p);return r
out=[bind(I/'manifest.json'),bind(I/'verification-receipt.json')]
m=json.loads((I/'manifest.json').read_text())
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={r['path'] for r in m['files']}|set(m['excluded_exact_paths'])
for r in m['files']:out.append(check(I/r['path'],r['sha256'],r['size']))
for r in json.loads((I/'bindings.json').read_text()):
 for k in ['original','copy']:out.append(check(pathlib.Path(r[k]),r['sha256'],r.get('bytes',r.get('size'))))
(L/'initial-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
M=L.parent/'pi-mathdb-full-corpus-inventory-r301'/'manifest.json'
print('inventory structure',json.loads(M.read_text()).keys())
print(json.dumps(json.loads(M.read_text()),indent=2)[:6500])
v=json.loads(M.read_text()); print('frozen schema',json.dumps(v['frozen_inputs'])[:3500])
for r in v['files']:
 if r['path'].startswith('corpus/'):out.append(check(M.parent/r['path'],r['sha256'],r['bytes']))
for r in v['frozen_inputs']:
 p=pathlib.Path(r.get('path',r.get('original','')));p=p if p.is_absolute() else M.parent/p
 out.append(check(p,r['sha256'],r.get('bytes',r.get('size'))))
(L/'initial-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('ALL 20 CHUNKS AND',len(v['frozen_inputs']),'INPUTS VERIFIED')
print('queue schema',json.dumps(json.loads((I/'queue-r686.json').read_text()))[:1800])
