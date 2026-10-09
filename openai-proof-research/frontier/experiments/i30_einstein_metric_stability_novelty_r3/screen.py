from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i30_einstein_metric_stability_novelty_r3'
base=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
patterns=[r'almost[- ]Einstein',r'Einstein.{0,100}(stability|Hausdorff|quantitative)',r'(distance[- ]distortion|material.{0,12}(volume|subset))',r'(Ricci|Riemannian).{0,50}(stability|rigidity)']
rows=[]
for pattern in patterns:
 r=subprocess.run(['rg','-n','-i','--glob','*.tex',pattern,str(base)],capture_output=True,text=True)
 hits=[]
 for line in r.stdout.splitlines():
  p,n,t=line.split(':',2);hits.append(dict(path=str(Path(p).relative_to(R)),line=int(n),text=t))
 rows.append(dict(pattern=pattern,hits=hits))
(S/'corpus-screen.json').write_text(json.dumps(dict(policy='Mechanical screening only, not semantic full-corpus reading',queries=rows),indent=2)+'\n')
for x in rows:
 names=sorted({Path(y['path']).parts[5] for y in x['hits']}); print(x['pattern'],len(x['hits']),names)
inventory=json.loads((R/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text())
titles=sorted({x['path'].split('/')[1] for x in inventory['files']})
normalized=[]
for entry in inventory['files']:
 if not entry['path'].endswith(('.tex','.md','.txt')): continue
 p=base/entry['path']; t=re.sub(r'\s+',' ',p.read_text(errors='replace'))
 for pattern in patterns:
  matches=[dict(offset=m.start(),text=t[max(0,m.start()-100):m.end()+180]) for m in re.finditer(pattern,t,re.I)]
  if matches: normalized.append(dict(path=str(p.relative_to(R)),pattern=pattern,matches=matches))
data=dict(policy='Mechanical normalized full-text and title screen; NOT semantic reading of 749 manuscripts. Existing cache reused read-only.',inventory_manuscripts=len(titles),inventory_text_files=len(inventory['files']),title_pattern='Einstein|Ricci|Riemannian|Kahler|Kähler|curvature|Gromov',title_matches=[t for t in titles if re.search('Einstein|Ricci|Riemannian|Kahler|Kähler|curvature|Gromov',t,re.I)],normalized_matches=normalized)
(S/'normalized-corpus-screen.json').write_text(json.dumps(data,indent=2)+'\n')
print('Normalized matched files:',sorted({x['path'].split('/')[5] for x in normalized}))
