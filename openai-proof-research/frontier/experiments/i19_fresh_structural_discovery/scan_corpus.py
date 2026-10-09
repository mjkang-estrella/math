#!/usr/bin/env python3
"""Read-only corpus search; no corpus files are copied or changed."""
import json,re,hashlib
from pathlib import Path
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i19_fresh_structural_discovery'
x=json.loads((S/'inputs/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json').read_text())
patterns=['unimodal','symmetric square','alternating square','weighted switch','edge activit','Lefschetz']
hits={};count=0
for a in x['files']:
 p=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'/a['path'];b=p.read_bytes()
 assert hashlib.sha256(b).hexdigest()==a['sha256'],a['path']
 t=b.decode(errors='replace');count+=1;hh=[]
 for term in patterns:
  for m in list(re.finditer(re.escape(term),t,re.I))[:3]:hh.append(dict(term=term,line=t[:m.start()].count('\n')+1,context=t[max(0,m.start()-90):m.end()+130]))
 if hh:hits[a['path']]=hh
(S/'corpus-search.json').write_text(json.dumps(dict(patterns=patterns,files_scanned=count,all_scanned_hashes_verified=True,hits=hits),indent=2)+'\n')
print(json.dumps(dict(files_scanned=count,hit_files=len(hits))))
