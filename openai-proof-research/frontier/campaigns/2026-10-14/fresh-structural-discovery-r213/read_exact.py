from pathlib import Path
import sys,json,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r213')
F={'A':'Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026','B':'Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026'}
for spec in sys.argv[1:]:
 kind,name,*bounds=spec.split(':')
 p=R/'private/pinned/preprints'/F[kind]/name
 b=p.read_bytes(); a=int(bounds[0]) if bounds else 0; z=min(int(bounds[1]),len(b)) if len(bounds)>1 else len(b)
 out=b[a:z].decode('utf8')
 print(f'--- {kind}/{name} BYTES [{a},{z})/{len(b)} ---')
 print(out)
 with (R/'private/read-extents.jsonl').open('a') as f:
  f.write(json.dumps({'path':str(p.relative_to(R)),'byte_start':a,'byte_end':z,'file_bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'kind':'semantic-display','truncation':'none at reader; tool output must be checked'})+'\n')
