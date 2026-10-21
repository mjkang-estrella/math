"""One-time packet-only manifest; never overwrite an existing seal."""
import hashlib,json,os,stat,sys
from pathlib import Path
OWN=Path.cwd()/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r121'
def make(root):
 assert root==OWN or OWN in root.parents
 assert not (root/'MANIFEST.json').exists(),'refuse reseal'
 assert {p.name for p in root.iterdir()}=={'packet','FINAL.md','REPORT.md'}
 files=[];dirs=['packet']
 for base,ds,fs in os.walk(root/'packet',followlinks=False):
  for name in ds:
   p=Path(base)/name;assert p.is_dir() and not p.is_symlink();dirs.append(p.relative_to(root).as_posix())
  for name in fs:
   p=Path(base)/name;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
   files.append({'path':p.relative_to(root).as_posix(),'size':s.st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
 m={'schema':'r121-packet-only-v1','outside_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'files':sorted(files,key=lambda x:x['path']),'directories':sorted(dirs)}
 with (root/'MANIFEST.json').open('x') as f:json.dump(m,f,indent=2);f.write('\n')
 print(json.dumps({'payload_files':len(files),'outside_envelopes':3,'total_files':len(files)+3,'directories':len(dirs)}))
if __name__=='__main__':make(Path(sys.argv[1]) if len(sys.argv)>1 else OWN)
