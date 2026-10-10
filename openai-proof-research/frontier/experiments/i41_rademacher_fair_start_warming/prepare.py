"""One-time acquisition metadata. Do not rerun after sealing."""
from pathlib import Path
import json,hashlib,re,shutil
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i41_rademacher_fair_start_warming'
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(p,x): p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
assert not (S/'artifact-seal.json').exists()
paths=sorted(p for p in R.rglob('*.md') if 'sources' not in p.relative_to(R).parts and 'experiments' not in p.relative_to(R).parts and 'i41-' not in p.name)
paths+= [R/'frontier/iterations/i40-critical-sk-waiting-relaxation.md',R/'frontier/sources/i40_critical_sk_waiting_relaxation/full-brief.txt',R/'frontier/sources/i40_critical_sk_waiting_relaxation/artifact-seal.json',R/'frontier/experiments/i40-parent-verification.json',R/'frontier/experiments/i40_critical_sk_waiting_relaxation/check.py',R/'frontier/experiments/i40_critical_sk_waiting_relaxation/verify.py',R/'sources/upstream.json',R/'sources/preprints-tree.json',R/'sources/CONTENTS.md',R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json',R/'frontier/experiments/i39-parent-verification.json',R/'frontier/sources/i39_quantum_spectral_discovery/full-brief.txt',R/'frontier/sources/i39_quantum_spectral_discovery/artifact-seal.json',R/'frontier/experiments/i39_quantum_spectral_discovery/check.py',R/'frontier/experiments/i39_quantum_spectral_discovery/verify.py']
paths=sorted(set(paths))
inputs=[]
for p in sorted(set(paths)):
 b=p.read_bytes();rel=str(p.relative_to(R));dst=S/'frozen'/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
 inputs.append({'path':rel,'bytes':len(b),'sha256':sha(b),'mutable':rel in ['frontier/TEN-FINDINGS.md','frontier/iterations/README.md']})
put(S/'inputs.json',inputs)
pattern=r'Sherrington|Kirkpatrick|quench|waiting.time|weak.*strong|warming|critical.*mixing|hidden.*mode'
hits=[]
for p in paths:
 if p.suffix!='.md' or 'sources' in p.relative_to(R).parts: continue
 found=[{'line':i,'text':v} for i,v in enumerate(p.read_text().splitlines(),1) if re.search(pattern,v,re.I)]
 if found:hits.append({'path':str(p.relative_to(R)),'matches':found})
put(S/'project-search.json',{'pattern':pattern,'files':[r['path'] for r in inputs if r['path'].endswith('.md') and '/sources/' not in r['path'] and not r['path'].startswith('sources/')],'matches':hits})
manifest=json.loads((R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text())
root=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'; patterns={'models':r'Sherrington|Kirkpatrick|critical quench|waiting.time','fair_start':r'fair.start|uniform.start|second.moment|inverse.partition|Feynman.Kac|multitime|multi.time', 'mechanisms':r'warming|low.energy compact|strong semigroup|uniform.*(waiting|Rademacher)|Rademacher.*(entropy|kernel|mixing)'}
audit={k:[] for k in patterns};selected=[]
for row in manifest['files']:
 b=(root/row['path']).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256']
 for k,pat in patterns.items():
  hit=[{'line':i,'text':v} for i,v in enumerate(b.decode(errors='replace').splitlines(),1) if re.search(pat,v,re.I)]
  if hit:audit[k].append({'path':row['path'],'matches':hit})
 if any(x in row['path'] for x in ['Universality-of-critical-quench','Functional-universality-of-critical-SK','Critical-mixing-in-the-Sherrington','A-spectral-gap-throughout-the-high-temperature','Critical-slowing-down-in-the-Sherrington']):selected.append(row)
put(S/'corpus-search.json',{'patterns':patterns,'matches':audit});put(S/'selected-pinned.json',selected)
print(json.dumps({'frozen_inputs':len(inputs),'project_hits':len(hits),'corpus_files':len(manifest['files']),'selected_files':len(selected)}))
