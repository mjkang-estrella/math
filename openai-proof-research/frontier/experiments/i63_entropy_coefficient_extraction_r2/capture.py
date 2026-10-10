"""One-shot I63 freeze. Writes only I63 assigned evidence directories."""
from pathlib import Path
import hashlib,json,subprocess,shutil
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i63_entropy_coefficient_extraction_r2'; A=R/'frontier/sources/i61_averaged_entropy_coefficient_rounding'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def save(p,x):
 p=S/p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x') as f:json.dump(x,f,indent=2,sort_keys=True);f.write('\n')
def copy(p,d):
 b=p.read_bytes();t=S/d;t.parent.mkdir(parents=True,exist_ok=True)
 with t.open('xb') as f:f.write(b)
 return dict(path=str(p.relative_to(R)),frozen=str(t.relative_to(R)),sha256=sha(b))
mutable=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
paths=['AGENTS.md',*mutable,'sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/iterations/iteration63-entropy-coefficient-extraction-r2-task.json','frontier/iterations/i61-averaged-entropy-coefficient-rounding.md','frontier/iterations/i59-dimension-uniform-entropy-stability.md','frontier/iterations/i53-sharp-entropy-stability-discovery.md','frontier/reviews/i55-sharp-entropy-stability-r2.md','frontier/reviews/i56-sharp-entropy-stability-novelty.md','frontier/experiments/i61-parent-verification.json']
rows=[]
for p in paths:
 row=copy(R/p,Path('inputs')/p);row['mutable']=p in mutable;rows.append(row)
save(Path('inputs.json'),rows)
task=json.loads((R/paths[8]).read_text())
(S/'brief.txt').write_text('Act as the review sub-agent for this task.\n\n'+task['brief'])
pins=[]
for row in json.loads((A/'pins.json').read_text())+json.loads((A/'additional-pins.json').read_text()):
 p=A/'pinned'/row['path'];r=copy(p,Path('pinned')/row['path']);r.update(upstream_path=row['path'],git_blob=blob(p.read_bytes()));pins.append(r)
save(Path('pins.json'),pins)
prior=[]
for stem in ['i53_sharp_entropy_stability_discovery','i55_sharp_entropy_stability_r2','i56_sharp_entropy_stability_novelty','i59_dimension_uniform_entropy_stability','i61_averaged_entropy_coefficient_rounding']:
 for base in ['frontier/sources','frontier/experiments']:
  for p in sorted((R/base/stem).rglob('*')):
   if p.is_file():prior.append(dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes())))
save(Path('prior-hashes.json'),prior)
briefs=[]
for stem in ['i53_sharp_entropy_stability_discovery','i55_sharp_entropy_stability_r2','i56_sharp_entropy_stability_novelty','i59_dimension_uniform_entropy_stability','i61_averaged_entropy_coefficient_rounding']:
 for name in ['brief.txt','objections.json','objections-and-responses.json']:
  p=R/'frontier/sources'/stem/name
  if p.exists():briefs.append(copy(p,Path('prior-records')/stem/name))
save(Path('prior-records.json'),briefs)
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'; inventory=[]
for n in sorted(subprocess.check_output(['rg','--files','--no-ignore','.'],cwd=C,text=True).splitlines()):
 n=n.removeprefix('./');b=(C/n).read_bytes();inventory.append(dict(path=n,sha256=sha(b),git_blob=blob(b)))
save(Path('corpus.json'),inventory)
patterns={'paired':'divided.difference|spectral clipping|fourth.moment','linked':'Frobenius algebra|coassociat|dephasing','entropy':'q\\^\\{-1\\}|coefficient-symmetry|coefficients-commute'}
searches=[]
for label,pattern in patterns.items():
 cp=subprocess.run(['rg','--no-ignore','-n','-i',pattern,'.'],cwd=C,text=True,capture_output=True);assert cp.returncode in [0,1]
 lines=sorted(cp.stdout.splitlines());save(Path('searches')/(label+'.json'),lines);searches.append(dict(label=label,pattern=pattern,lines=len(lines),domain=str(C.relative_to(R))))
save(Path('searches.json'),searches)
print(json.dumps(dict(inputs=len(rows),pins=len(pins),prior=len(prior),briefs=len(briefs),corpus=len(inventory),searches=searches),indent=2))
