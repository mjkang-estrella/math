"""One-shot I64 input/corpus/search capture. Never changes an earlier round."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i64_entropy_coefficient_extraction_novelty'
def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def write(p,x):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x') as f: json.dump(x,f,indent=2);f.write('\n')
mutable=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
paths=mutable+['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/iterations/iteration64-entropy-coefficient-extraction-novelty-task.json','frontier/iterations/i61-averaged-entropy-coefficient-rounding.md','frontier/iterations/i59-dimension-uniform-entropy-stability.md','frontier/iterations/i53-sharp-entropy-stability-discovery.md','frontier/reviews/i55-sharp-entropy-stability-r2.md','frontier/reviews/i56-sharp-entropy-stability-novelty.md','frontier/experiments/i61_averaged_entropy_coefficient_rounding/verify.py']
rows=[]
for name in paths:
 b=(R/name).read_bytes();p=S/'inputs'/name;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(b)
 rows.append(dict(path=name,sha256=sha(b),mutable=name in mutable))
write(S/'inputs.json',rows)
task=json.loads((R/paths[8]).read_text())
with (S/'brief.txt').open('x') as f:f.write('Act as the review sub-agent for this task.\n\n'+task['brief'])
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus';tree=json.loads((R/'sources/preprints-tree.json').read_text())['tree'];idx={r['path']:r for r in tree}
files=sorted(x.removeprefix('./') for x in subprocess.check_output(['rg','--files','--no-ignore','.'],cwd=C,text=True).splitlines()); inv=[]
for name in files:
 b=(C/name).read_bytes();g=blob(b);assert g==idx[name]['sha'];inv.append(dict(path=name,sha256=sha(b),git_blob=g))
assert len(tree)==13223 and len(files)==9340
write(S/'corpus.json',inv);write(S/'manuscripts.json',sorted({p['path'].split('/')[1] for p in tree}))
prior=[]
for root in ['frontier/sources/i61_averaged_entropy_coefficient_rounding','frontier/experiments/i61_averaged_entropy_coefficient_rounding','frontier/sources/i59_dimension_uniform_entropy_stability','frontier/experiments/i59_dimension_uniform_entropy_stability','frontier/sources/i53_sharp_entropy_stability_discovery','frontier/experiments/i53_sharp_entropy_stability_discovery','frontier/sources/i55_sharp_entropy_stability_r2','frontier/experiments/i55_sharp_entropy_stability_r2','frontier/sources/i56_sharp_entropy_stability_novelty','frontier/experiments/i56_sharp_entropy_stability_novelty']:
 for p in sorted((R/root).rglob('*')):
  if p.is_file():prior.append(dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes())))
write(S/'prior-hashes.json',prior)
patterns={'compatibility':r'paired.{0,35}(spectral|curl)|curl.{0,50}(matrix|Hessian|coefficient)|Hessian.{0,50}compatib|divided.{0,12}difference', 'moments':r'fourth.moment|spectral.{0,20}(clip|truncat)|row.column|noncommutative.{0,10}compact', 'algebras':r'almost.commut|approximate.{0,20}(Frobenius|associativ)|orthogonally.decompos|tensor.{0,20}(truncat|round)'}
search=[]
for label,pattern in patterns.items():
 cp=subprocess.run(['rg','--no-ignore','-n','-i',pattern,'.'],cwd=C,text=True,capture_output=True);assert cp.returncode in [0,1]
 lines=sorted(cp.stdout.splitlines());write(S/'searches'/(label+'.json'),lines);search.append(dict(label=label,pattern=pattern,lines=len(lines)))
write(S/'searches.json',search)
pins=json.loads((R/'frontier/sources/i61_averaged_entropy_coefficient_rounding/pins.json').read_text())+json.loads((R/'frontier/sources/i61_averaged_entropy_coefficient_rounding/additional-pins.json').read_text())
for row in pins:
 b=(C/row['path']).read_bytes();p=S/'pinned'/row['path'];p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(b)
write(S/'pins.json',pins)
print(json.dumps(dict(inputs=len(rows),prior_files=len(prior),corpus=len(inv),manuscripts=749,searches=search)))
