from pathlib import Path
import hashlib,json,shutil
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i23_kinetic_connected_fluctuations'
sha=lambda b:hashlib.sha256(b).hexdigest()
inputs=['AGENTS.md','frontier/TEN-FINDINGS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/iterations/i20-pde-kinetic-discovery.md','frontier/sources/i20_pde_kinetic_discovery/full-brief.txt','frontier/sources/i20_pde_kinetic_discovery/pinned-manifest.json','frontier/sources/i20_pde_kinetic_discovery/reading-locators.json','frontier/sources/i20_pde_kinetic_discovery/statement-contracts.json']
m=[]
for p in inputs:
 b=(ROOT/p).read_bytes(); dst=S/'inputs'/p;dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists(): assert dst.read_bytes()==b, p
 else:dst.write_bytes(b)
 m.append(dict(path=p,sha256=sha(b),bytes=len(b),shared=p in ['frontier/TEN-FINDINGS.md']))
(S/'input-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
old=ROOT/'frontier/sources/i20_pde_kinetic_discovery'
manifest=json.loads((old/'pinned-manifest.json').read_text());selected=[]
for x in manifest['files']:
 if any(k in x['path'] for k in ['Hard-sphere-fluctuations-on-the-regular','The-Boltzmann-Grad-limit-for-stable']):
  b=(old/'corpus'/x['path']).read_bytes();assert sha(b)==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']
  dst=S/'corpus'/x['path'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b);selected.append(x)
(S/'pinned-manifest.json').write_text(json.dumps(dict(pin=manifest['pin'],files=selected),indent=2)+'\n')
print('Frozen',len(m),'inputs and',len(selected),'pinned H/P source files')
