"""One-time local research-packet byte seal; never a mathematical gate."""
from pathlib import Path
import hashlib,json,os,stat
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r149')
OUT=['FINAL.md','MANIFEST.json','REPORT.md']
entries=[]
for base,ds,fs in os.walk(R,followlinks=False):
 for n in ds:
  p=Path(base)/n
  if p.is_symlink():raise ValueError('symlink directory')
 for n in fs:
  p=Path(base)/n;rel=p.relative_to(R).as_posix();s=p.lstat()
  if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('nonregular/hardlink')
  if rel in OUT:continue
  b=p.read_bytes();entries.append({'path':rel,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
obj={'schema':'r149-exact-payload-v1','outside_envelopes':OUT,'files':sorted(entries,key=lambda x:x['path'])}
with (R/'MANIFEST.json').open('x') as f:f.write(json.dumps(obj,indent=2)+'\n')
print('SEALED',len(entries),'payloads;',len(entries)+3,'total regular files')
for n in OUT:print(n,hashlib.sha256((R/n).read_bytes()).hexdigest())
