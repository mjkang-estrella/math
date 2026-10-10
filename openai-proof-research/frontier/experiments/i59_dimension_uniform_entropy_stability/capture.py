"""One-time capture. Writes only I59 paths; never used by offline verifier."""
from pathlib import Path
import hashlib, json, subprocess, shutil

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i59_dimension_uniform_entropy_stability'
def sha(b): return hashlib.sha256(b).hexdigest()
def save(name,obj):
    p=S/name; p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
if (S/'inputs.json').exists(): raise SystemExit('Refuse to overwrite original capture')
mutable=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
inputs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',
 'frontier/iterations/iteration59-dimension-uniform-entropy-stability-task.json',
 'frontier/iterations/i53-sharp-entropy-stability-discovery.md',
 'frontier/reviews/i55-sharp-entropy-stability-r2.md',
 'frontier/reviews/i56-sharp-entropy-stability-novelty.md']+mutable
rows=[]
for name in inputs:
    b=(ROOT/name).read_bytes(); dst=S/'inputs'/name; dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(b)
    rows.append(dict(path=name,sha256=sha(b),mutable=name in mutable))
save('inputs.json',rows)
brief=json.loads((ROOT/inputs[4]).read_text())['brief']
(S/'brief.txt').write_text('Act as the research sub-agent for this task.\n\n'+brief)
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree']; idx={x['path']:x for x in tree}
corpus=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
paths=sorted(subprocess.check_output(['rg','--files','--no-ignore','.'],cwd=corpus,text=True).splitlines())
inventory=[]
for name in paths:
    name=name.removeprefix('./'); b=(corpus/name).read_bytes()
    inventory.append(dict(path=name,sha256=sha(b),git_blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()))
save('corpus.json',inventory)
save('coverage.json',dict(tree_entries=len(tree),manuscripts=len({x['path'].split('/')[1] for x in tree}),corpus_files=len(inventory)))
prior=ROOT/'frontier/sources/i53_sharp_entropy_stability_discovery/pinned'
pins=[]
for p in sorted(prior.rglob('*')):
    if not p.is_file(): continue
    name=str(p.relative_to(prior)); b=p.read_bytes(); blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert blob==idx[name]['sha']
    dest=S/'pinned'/name; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(b)
    pins.append(dict(path=name,sha256=sha(b),git_blob=blob,url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+name))
save('pins.json',pins)
queries=[('uniform','entropy.{0,60}stability|stability.{0,60}entropy|almost.commut|orthogonally.decompos'),
 ('slack','covariance.completion|strict.remainder|final.polynomial|spectral.identity|first.chaos'),
 ('probability','simplex.{0,50}stability|Borell|Berwald|localization.{0,50}entropy|entropy.{0,50}localization')]
search=[]
for label,pattern in queries:
    cp=subprocess.run(['rg','--no-ignore','-n','-i',pattern,'.'],cwd=corpus,text=True,capture_output=True)
    assert cp.returncode in (0,1)
    lines=sorted(cp.stdout.splitlines()); save('searches/'+label+'.json',lines)
    search.append(dict(label=label,pattern=pattern,lines=len(lines)))
save('searches.json',search)
prior_hashes=[]
for rel in ['frontier/sources/i53_sharp_entropy_stability_discovery','frontier/experiments/i53_sharp_entropy_stability_discovery',
 'frontier/sources/i55_sharp_entropy_stability_r2','frontier/experiments/i55_sharp_entropy_stability_r2',
 'frontier/sources/i56_sharp_entropy_stability_novelty','frontier/experiments/i56_sharp_entropy_stability_novelty']:
    for p in sorted((ROOT/rel).rglob('*')):
        if p.is_file(): prior_hashes.append(dict(path=str(p.relative_to(ROOT)),sha256=sha(p.read_bytes())))
save('prior-hashes.json',prior_hashes)
print(json.dumps(dict(inputs=len(rows),pins=len(pins),prior_files=len(prior_hashes),searches=search)))
