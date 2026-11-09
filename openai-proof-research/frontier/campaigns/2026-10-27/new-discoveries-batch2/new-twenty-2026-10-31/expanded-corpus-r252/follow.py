from pathlib import Path
import json,re
L=Path(__file__).resolve().parent;D=L/'http';j=[]
t=json.loads((D/'omega-tree.json').read_text())
# A truncated recursive tree does not enumerate all top-level names. Request nonrecursive root.
j.append(['omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/1c3e22220746be4f0b18e51689b333dc025c36ab'])
if (D/'openai-preprints-complete.json').exists():
 t=json.loads((D/'openai-preprints-complete.json').read_text());print('preprints truncated',t.get('truncated'))
 for x in t.get('tree',[]):
  p=x['path']
  if re.search(r'hamada|queen|stahl|kneser|gessel|peak|star.forest|transversal|latin|polyhedral|antidirect|agrawal|triple.array|triangle.free.*cycl|adjacency.dimension|extendab|bow.tie|wheel|immersion|mubayi|regular.subgraph|skew.symmetr|signed.permutation|spectral.radius',p,re.I) and x['type']=='blob':
   print('MATCH',p)
   if p.endswith('.tex'):j.append(['oai-'+p.replace('/','--'),f'https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/{p}'])
(L/'follow-plan.json').write_text(json.dumps(j))
