"""One-shot exact seal builder for this root or its independent reduced controls."""
import hashlib,json,os,stat,sys
from pathlib import Path
E={'FINAL.md','MANIFEST.json','REPORT.md'}
def seal(root):
 assert not (root/'MANIFEST.json').exists(),'seal already exists'
 files={};dirs=[]
 for parent,ds,fs in os.walk(root,followlinks=False):
  ds.sort();fs.sort()
  for n in ds:
   p=Path(parent)/n;assert stat.S_ISDIR(p.lstat().st_mode);dirs.append(p.relative_to(root).as_posix())
  for n in fs:
   p=Path(parent)/n;rel=p.relative_to(root).as_posix();s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
   if rel in E:continue
   b=p.read_bytes();files[rel]={'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 m={'format':'r124-exact-v1','outside_envelopes':sorted(E),'directories':sorted(dirs),'files':dict(sorted(files.items()))}
 (root/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
 return {n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in sorted(E)}
if __name__=='__main__':print(json.dumps(seal(Path(sys.argv[1])),indent=2))
