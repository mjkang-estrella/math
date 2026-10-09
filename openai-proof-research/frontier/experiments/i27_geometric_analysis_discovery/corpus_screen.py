"""Complete normalized-text discovery screen; matches are not theorem claims."""
from pathlib import Path
import json,re,collections
ROOT=Path(__file__).resolve().parents[3];C=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus';S=ROOT/'frontier/sources/i27_geometric_analysis_discovery'
patterns={'einstein-stability':r'(?i)(almost.{0,30}einstein|einstein.{0,60}(stabil|gap|compact|defect))','varifold-endpoint':r'(?i)(varifold.{0,80}(rectifi|singular)|singular.{0,80}varifold)','ricci-extension-broad':r'(?i)(scalar.{0,70}(extension|continuation)|ricci.{0,50}tree)','ricci-extension-focused':r'(?i)(\bricci[- ]flow.{0,90}(scalar|extension|continuation)|\bricci[- ]flat.{0,60}tree)'}
res={k:[] for k in patterns};compiled={k:re.compile(v) for k,v in patterns.items()};manifest=json.loads((S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text())
for x in sorted(manifest['files'],key=lambda x:x['path']):
 s=' '.join((C/x['path']).read_text().split())
 for k,pat in compiled.items():
  mm=list(pat.finditer(s))
  if mm:res[k].append({'path':x['path'],'count':len(mm),'samples':[s[max(0,m.start()-80):m.end()+100] for m in mm[:3]]})
out={'patterns':patterns,'coverage_files':len(manifest['files']),'hits':res,'limitations':'Broad matches include scalar extension in unrelated algebra. Selected geometry is screened using exact source contracts; no negative-match priority inference.'}
(S/'corpus-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:{'files':len(v),'manuscripts':len({x['path'].split('/')[1] for x in v})} for k,v in res.items()}))
