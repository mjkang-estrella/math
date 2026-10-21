"""One-shot root manifest writer. Never rerun after real-root sealing."""
from pathlib import Path
import os,stat,json,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r117');assert not (R/'MANIFEST.json').exists()
def H(p):b=p.read_bytes();return {'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
files={};dirs=[]
for d,ds,fs in os.walk(R):
 for n in sorted(ds+fs):
  p=Path(d)/n;s=p.lstat();rel=p.relative_to(R).as_posix();assert not stat.S_ISLNK(s.st_mode)
  if p.is_dir():dirs.append(rel)
  else:
   assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
   files[rel]=H(p)
assert set(x for x in files if not x.startswith('packet/'))=={'FINAL.md','REPORT.md'}
m={'format':'r117-exact-v1','payload_files':{k:v for k,v in sorted(files.items()) if k.startswith('packet/')},'envelopes':{n:files[n] for n in ['FINAL.md','REPORT.md']},'directories':sorted(dirs),'scope':'Exact own membership. No inherited input manifest. Byte checks are not mathematical gates.'}
(R/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n')
print(json.dumps({'payload_files':len(m['payload_files']),'whole_files':len(files)+1,'directories':len(dirs),'detached':{n:H(R/n)['sha256'] for n in ['FINAL.md','MANIFEST.json','REPORT.md']}},indent=2))
