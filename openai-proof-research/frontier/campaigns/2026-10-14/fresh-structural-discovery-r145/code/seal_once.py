"""Seal this root exactly once. The three outer-envelope hashes must be detached."""
from pathlib import Path
import hashlib,json,os,datetime
R=Path(__file__).resolve().parents[1];outer={'FINAL.md','MANIFEST.json','REPORT.md'}
if (R/'MANIFEST.json').exists():raise SystemExit('Already sealed; refusing to replace manifest')
files={};dirs=[]
for parent,ds,fs in os.walk(R,followlinks=False):
 for name in ds+fs:
  if (Path(parent)/name).is_symlink():raise SystemExit('Symlinks forbidden')
 dirs.extend(str((Path(parent)/d).relative_to(R)) for d in ds)
 for f in fs:
  p=Path(parent)/f;rel=str(p.relative_to(R))
  if rel not in outer:files[rel]={'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
manifest={'format':'r145-exact-membership-v1','scope':'entire actual r145 root excluding exactly three detached outer envelopes','created':datetime.datetime.now(datetime.timezone.utc).isoformat(),'outer_envelopes':sorted(outer),'files':dict(sorted(files.items())),'directories':sorted(dirs)}
with (R/'MANIFEST.json').open('x') as f:f.write(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'payload_files':len(files),'directories':len(dirs),'outer_envelopes':3}))
for name in ['FINAL.md','MANIFEST.json','REPORT.md']:
 print(hashlib.sha256((R/name).read_bytes()).hexdigest(),name)
