from pathlib import Path
import json,hashlib,shutil,datetime
R=Path.cwd(); S=R/'frontier/sources/i26_probability_discovery'; C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'; pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
inputs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/TEN-FINDINGS.md','frontier/iterations/i09-potts-fiid-screen.md','frontier/iterations/i13-fresh-discovery.md','frontier/iterations/i17-fresh-discovery.md','frontier/iterations/i20-pde-kinetic-discovery.md','frontier/iterations/i23-kinetic-connected-fluctuations.md','frontier/reviews/i15-odd-order-topology-novelty-r3.md','frontier/reviews/i17-six-point-ramsey-novelty-r3.md','frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json']
manifest=[]
for p in inputs:
 b=(R/p).read_bytes(); dest=S/'inputs'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);manifest.append(dict(path=p,sha256=sha(b),bytes=len(b)))
(S/'input-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
keys=['Cardys-formula','Pivotal-Amplitude','From-critical-crossings','Logarithmic-Relative','Quenched-SLE','Gaussian-free-field-limits-of-weighted','The-Gaussian-free-field-limit-of-integer','Critical-bond-and-site','Spectral-convergence-for-critical','Random-Walks-on-Critical','Thermal-FK-Ising','Buffered-comparison','SLE3-universality-for-weak','Conformal-universality-of-bulk-Ising','Uniform-real-Lipschitz']
tree=json.loads((R/'sources/preprints-tree.json').read_text());old={x['path']:x for x in json.loads((R/inputs[-1]).read_text())['files']};ms=[]
for x in tree['tree']:
 p=x['path']
 if x['type']!='blob' or not any(k in p for k in keys) or not p.endswith(('.tex','.bib','.md')):continue
 b=(C/p).read_bytes();g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(); assert g==x['sha'] and sha(b)==old[p]['sha256']
 dest=S/'pinned'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 ms.append(dict(path=p,url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+p,git_blob=g,sha256=sha(b),bytes=len(b),retrieval='verified read-only cache; snapshot '+datetime.datetime.now(datetime.timezone.utc).isoformat()))
(S/'pinned-manifest.json').write_text(json.dumps(dict(pin=pin,files=ms),indent=2)+'\n')
(S/'inventory-screen.json').write_text(json.dumps(dict(entries=len(tree['tree']),truncated=tree.get('truncated'),manuscripts=[x['path'] for x in tree['tree'] if x['type']=='tree' and x['path'].count('/')==1],selected_manuscripts=sorted(set(x['path'].split('/')[1] for x in ms)),selection_keys=keys),indent=2)+'\n')
print('Frozen',len(inputs),'inputs and',len(ms),'selected texts from',len(set(x['path'].split('/')[1] for x in ms)),'manuscripts')
