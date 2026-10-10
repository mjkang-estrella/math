from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i38_propeller_stability_novelty_r3'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','frontier/TEN-FINDINGS.md','frontier/iterations/README.md','frontier/iterations/i38-inequality-stability-discovery.md','frontier/reviews/i38-propeller-stability-r2.md','frontier/reviews/i25-rooted-entropy-novelty-r3.md','frontier/reviews/i30-einstein-metric-stability-novelty-r3.md','frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md','frontier/iterations/iteration38-inequality-stability-discovery-task.json','frontier/iterations/iteration38-propeller-stability-proof-r2-task.json','frontier/experiments/i38-parent-verification.json','frontier/experiments/i38-r2-parent-verification.json']
a=[]
for name in files:
 p=R/name
 if not p.exists():continue
 dest=S/'frozen'/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 a.append({'path':name,'frozen':str(dest.relative_to(R)),'sha256':sha(p),'mutable':name in ['frontier/TEN-FINDINGS.md','frontier/iterations/README.md']})
(S/'input-manifest.json').write_text(json.dumps(a,indent=2)+'\n')
b=[]
for stem in ['i38_inequality_stability_discovery','i38_propeller_stability_r2']:
 for category in ['sources','experiments']:
  for p in sorted((R/'frontier'/category/stem).rglob('*')):
   if p.is_file() and '__pycache__' not in p.parts:b.append({'path':str(p.relative_to(R)),'bytes':p.stat().st_size,'sha256':sha(p)})
for name in ['frontier/iterations/i38-inequality-stability-discovery.md','frontier/reviews/i38-propeller-stability-r2.md']:
 p=R/name;b.append({'path':name,'bytes':p.stat().st_size,'sha256':sha(p)})
(S/'prior-before.json').write_text(json.dumps(b,indent=2)+'\n')
(S/'.gitignore').write_text('literature/*.pdf\nliterature/*.txt\nliterature/*.html\nliterature/*.png\n')
print({'inputs':len(a),'prior_files':len(b)})
