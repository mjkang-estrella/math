"""Run once after all payload/envelope writes. Prints detached anchors; no anchor file."""
import hashlib,json,os,stat
from pathlib import Path
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r118')
M=R/'MANIFEST.json'
if M.exists():raise SystemExit('Refusing to reseal an existing manifest')
env={'FINAL.md','REPORT.md','MANIFEST.json'};files={};dirs=[];stack=[R]
while stack:
 d=stack.pop()
 for e in os.scandir(d):
  p=Path(e.path);rel=p.relative_to(R).as_posix();s=p.lstat()
  if stat.S_ISDIR(s.st_mode):dirs.append(rel);stack.append(p)
  elif stat.S_ISREG(s.st_mode) and s.st_nlink==1:
   if rel not in env:files[rel]={'size':s.st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
  else:raise SystemExit('Unsafe entry: '+rel)
M.write_text(json.dumps({'schema':'r118-exact-v1','files':files,'directories':sorted(dirs),'limits':'Own selection only; outside-packet envelopes use detached anchors; permissions not bound; no mathematical certification.'},sort_keys=True,indent=2)+'\n')
for n in ['FINAL.md','MANIFEST.json','REPORT.md']:print(n,hashlib.sha256((R/n).read_bytes()).hexdigest())
print('payload files',len(files),'directories',len(dirs))
