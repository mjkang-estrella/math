from pathlib import Path
import json,re
D=Path(__file__).resolve().parents[1]
terms=['arbor','evil','domatic','retrieval','zero-diagonal','bumpless','fork-free','banica','separating','circular-flow','common-zero','schutzen','neighborhood-ideal','seymour','colour-balanced','color-balanced','combinatorial-matrices','robin','dirichlet-to-neumann']
out={}
for f in ['omega-D5','omega-Problems','openai-preprints']:
 o=json.loads((D/f'sources/{f}.json').read_text()); matches=[]
 for t in o['tree']:
  p=t['path'].lower()
  hits=[s for s in terms if s in p]
  if hits:matches.append({'path':t['path'],'hits':hits,'sha':t['sha'],'type':t['type']})
 out[f]={'truncated':o['truncated'],'matches':matches};print(f,json.dumps(matches,indent=1)[:15000])
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
