"""Create the sole final-root membership manifest; refuses to overwrite."""
from pathlib import Path
import os,json,hashlib,stat
R=Path.cwd()/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r115'
E=['FINAL.md','MANIFEST.json','REPORT.md'];files={};dirs=[]
for base,ds,fs in os.walk(R,followlinks=False):
 for n in ds+fs:
  p=Path(base)/n;s=p.lstat();rel=p.relative_to(R).as_posix()
  if stat.S_ISLNK(s.st_mode):raise ValueError('symlink')
  if stat.S_ISDIR(s.st_mode):dirs.append(rel)
  elif stat.S_ISREG(s.st_mode) and s.st_nlink==1:
   if rel not in E:
    b=p.read_bytes();files[rel]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
  else:raise ValueError('nonregular or hardlink')
m={'format':'r115-exact-v1','outside_envelopes':E,'files':files,'directories':sorted(dirs)}
with (R/'MANIFEST.json').open('x') as f:f.write(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({'payload_files':len(files),'outside_envelopes':3,'directories':len(dirs)}))
for n in E:print(n,hashlib.sha256((R/n).read_bytes()).hexdigest())
