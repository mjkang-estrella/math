"""One-time evidence assembly; writes only the assigned I55 evidence directory."""
from pathlib import Path
import json,hashlib,subprocess,datetime
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i55_sharp_entropy_stability_r2'; A=R/'frontier/sources/i53_sharp_entropy_stability_discovery'
if (S/'inputs.json').exists(): raise SystemExit('Refusing to overwrite frozen I55 inputs')
def sha(b): return hashlib.sha256(b).hexdigest()
def save(n,o): (S/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
paths=['AGENTS.md','README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/iterations/i53-sharp-entropy-stability-discovery.md','frontier/iterations/iteration55-sharp-entropy-stability-r2-task.json']
inputs=[]
for p in paths:
 b=(R/p).read_bytes(); dest=S/'inputs'/p; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(b)
 inputs.append({'path':p,'frozen':str(dest.relative_to(R)),'sha256':sha(b)})
save('inputs.json',inputs)
brief=json.loads((R/paths[-1]).read_text())['brief']; (S/'brief.txt').write_text('Act as the review sub-agent for this task.\n\n'+brief+'\n')
files=[R/'frontier/iterations/i53-sharp-entropy-stability-discovery.md']
for d in (A,R/'frontier/experiments/i53_sharp_entropy_stability_discovery'):
 files+=sorted(p for p in d.rglob('*') if p.is_file())
save('author-files.json',{str(p.relative_to(R)):sha(p.read_bytes()) for p in files})
for name in ['seal.json','seal-initial.json','verification.json','verification-initial.json','validation-history.json','objections.json','brief.txt','passages.json','pinned-manifest.json']:
 dest=S/'inputs/author-records'/name; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes((A/name).read_bytes())
C='frontier/sources/i14_spectral_width_novelty_r3/corpus'
r=subprocess.run(['rg','--files','--no-ignore',C],cwd=R,capture_output=True,check=True)
ps=sorted(r.stdout.decode().splitlines()); save('corpus-inventory.json',[[p,sha((R/p).read_bytes())] for p in ps])
tree=json.loads((R/'sources/preprints-tree.json').read_text()); manuscripts=sorted({x['path'].split('/')[1] for x in tree['tree'] if x['path'].startswith('preprints/')})
save('manuscripts.json',manuscripts)
patterns={'compatibility':r'(entropy.{0,50}stabil|stabil.{0,50}entropy|almost.commut|orthogonal.{0,12}decompos.{0,12}tensor|linear-jacobian|coefficient-symmetry)', 'companions':r'(isotropic|simplex.{0,60}(stabil|constant)|commut.{0,50}(tensor|matri)|entropy.{0,60}(covariance|log.concave))'}
searches=[]
for name,pat in patterns.items():
 r=subprocess.run(['rg','--no-ignore','-n','-i',pat,C],cwd=R,capture_output=True)
 lines=sorted(r.stdout.decode().splitlines()); save(name+'-multiset.json',lines)
 searches.append({'name':name,'pattern':pat,'returncode':r.returncode,'stderr':r.stderr.decode(),'hits':len(lines)})
save('searches.json',searches)
save('capture.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'tree_entries':len(tree['tree']),'manuscripts':len(manuscripts),'corpus_files':len(ps),'scope':'No edits to upstream, author, prior, or shared paths.'})
print(json.dumps({'inputs':len(inputs),'author_files':len(files),'tree_entries':len(tree['tree']),'manuscripts':len(manuscripts),'corpus_files':len(ps),'searches':searches},indent=2))
