from pathlib import Path
import json,re,hashlib
root=Path(__file__).resolve().parents[3];s=root/'frontier/sources/i145_arithmetic_automorphic_discovery'
domain=json.loads((root/'frontier/sources/i112_inverse_boundary_discovery/search-domain.json').read_text())
patterns={'arithmetic_automorphic':r'(?i)(pro[- ]?modular|Fontaine.?Mazur|Arthur.{0,35}(project|filtrat|decompos)|torus.{0,25}packet|packet.{0,25}torus)', 'packet_relative':r'(?i)(subpacket|subcollection|class.{0,15}group.{0,30}(coset|subgroup)|coset.{0,40}(class|packet)|shortest.{0,45}(moment|integrab)|torus.{0,40}(effective|rate)|packet.{0,45}(correlation|uniform|shrinking))'}
rx={k:re.compile(v) for k,v in patterns.items()};out={k:[] for k in rx}
for r in domain:
 for i,l in enumerate((root/r['local']).read_bytes().decode('utf-8',errors='replace').splitlines(),1):
  for k,v in rx.items():
   mm=list(v.finditer(l))
   if mm:out[k].append(dict(path=r['path'],local=r['local'],splitlines_line=i,text=l,spans=[list(m.span()) for m in mm]))
(s/'lexical-search.json').write_text(json.dumps(dict(patterns=patterns,results=out),indent=2)+'\n')
print({k:len(v) for k,v in out.items()});print('\n'.join(sorted(set(r['path'].split('/')[1] for r in out['packet_relative']))))
