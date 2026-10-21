"""One-time final payload manifest; envelope hashes must be computed independently."""
from pathlib import Path
import hashlib,json,stat
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r116')
assert not (R/'MANIFEST.json').exists(),'already sealed'
files={};dirs=[]
for p in sorted((R/'packet').rglob('*')):
 s=p.lstat();rel=p.relative_to(R).as_posix()
 if stat.S_ISDIR(s.st_mode):dirs.append(rel)
 else:
  assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
  b=p.read_bytes();files[rel]={'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
dirs.append('packet')
(R/'MANIFEST.json').write_text(json.dumps({'schema':'r116-exact-payload-v1','directories':sorted(dirs),'files':files},sort_keys=True,indent=2)+'\n')
print(json.dumps({'payload_files':len(files),'directories':len(dirs),'outside_envelopes':3}))
