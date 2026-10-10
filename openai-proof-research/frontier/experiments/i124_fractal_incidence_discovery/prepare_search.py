"""One preparation search; no corpus copies. Final verifier recomputes it."""
from pathlib import Path
import json,re,hashlib
S=Path('frontier/sources/i124_fractal_incidence_discovery')
D=json.loads(Path('frontier/sources/i112_inverse_boundary_discovery/search-domain.json').read_text())
pat={'fractal_incidence':r'(?i)(?:pinned|pinning).{0,90}(?:distance|Falconer)|(?:Falconer|distance).{0,90}(?:pinned|pinning)|(?:Riemannian|nonlinear).{0,50}distance|(?:distance.{0,35}(?:exceptional|configuration)|(?:exceptional|configuration).{0,35}distance)'}
out={k:[] for k in pat};compiled={k:re.compile(v) for k,v in pat.items()}
for x in D:
 for i,l in enumerate(Path(x['local']).read_text(errors='replace').splitlines(),1):
  for k,r in compiled.items():
   m=list(r.finditer(l))
   if m:out[k].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=l,spans=[list(z.span()) for z in m]))
(S/'lexical-search.json').write_text(json.dumps(dict(patterns=pat,results=out),indent=2)+'\n')
expr=r'(?i)falconer|kakeya|distance|incidence|configuration|projection|furstenberg'
titles=sorted({x['path'].split('/')[1] for x in D if re.search(expr,x['path'].split('/')[1])})
(S/'title-screen.json').write_text(json.dumps(dict(expression=expr,titles=titles),indent=2)+'\n')
print('matched lines', {k:len(v) for k,v in out.items()})
from collections import Counter
print(Counter(x['path'].split('/')[1] for x in out['fractal_incidence']).most_common(20))
for title in ['The-higher-dimensional-Erdos-distinct-distances','A-power-saving-for-planar-unit-distances']:
 for x in D:
  if title in x['path'] and x['path'].endswith('introduction.tex'):print(x['local'])
