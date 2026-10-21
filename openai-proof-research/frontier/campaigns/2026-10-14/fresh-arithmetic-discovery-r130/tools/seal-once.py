"""Create only this packet's manifest once, after content and copied controls are final."""
from pathlib import Path
import hashlib,json,os,stat
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r130')
ENV=['envelopes/FINAL.md','envelopes/MANIFEST.json','envelopes/REPORT.md']
files={};dirs=[]
for b,ds,fs in os.walk(R,topdown=True,followlinks=False):
 for n in ds:
  p=Path(b)/n;assert not p.is_symlink() and p.is_dir();dirs.append(p.relative_to(R).as_posix())
 for n in fs:
  p=Path(b)/n;st=p.lstat();assert stat.S_ISREG(st.st_mode) and st.st_nlink==1
  rel=p.relative_to(R).as_posix()
  if rel not in ENV:files[rel]={'bytes':st.st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
m={'schema':'r130-exact-v1','excluded_envelopes':ENV,'files':dict(sorted(files.items())),'directories':sorted(dirs),'limits':'Bytes and exact membership only. No modes/timestamps/atomicity, mathematical gate or perfect-isolation certificate.'}
with (R/ENV[1]).open('x') as f:f.write(json.dumps(m,indent=2)+'\n')
print(json.dumps({'payload_files':len(files),'directories':len(dirs),'envelopes':3}))
for e in ENV:print(e,hashlib.sha256((R/e).read_bytes()).hexdigest())
