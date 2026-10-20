"""Create one artifact manifest. Refuses an already sealed root."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
if (R/'MANIFEST.json').exists() or (R/'DETACHED.json').exists():raise SystemExit('Already sealed; refusing to reseal')
OUT={'MANIFEST.json','FINAL.md','REPORT.md','DETACHED.json'}
rows=[]
for f in sorted(R.rglob('*')):
 if f.is_symlink():raise SystemExit('Symlink refused')
 if f.is_file() and str(f.relative_to(R)) not in OUT:
  b=f.read_bytes();rows.append(dict(path=str(f.relative_to(R)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
rows.sort(key=lambda x:x['path'])
(R/'MANIFEST.json').write_text(json.dumps(dict(schema='r136-exact-artifact-manifest-v1',outside_manifest=sorted(OUT),files=rows),indent=2)+'\n')
anchors={name:hashlib.sha256((R/name).read_bytes()).hexdigest() for name in ['MANIFEST.json','FINAL.md','REPORT.md']}
(R/'DETACHED.json').write_text(json.dumps(anchors,indent=2)+'\n')
print(json.dumps(anchors,indent=2))
