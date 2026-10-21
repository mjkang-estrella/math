"""Read-only exact-packet replay. Requires externally supplied detached anchors."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}
def digest(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={};directories=['.']
 for d,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in ds:
   p=Path(d)/name
   assert not p.is_symlink(), 'symlink directory'
   directories.append(p.relative_to(root).as_posix())
  for name in fs:
   p=Path(d)/name;rel=p.relative_to(root).as_posix()
   if rel in ENVELOPES:continue
   info=p.lstat();assert stat.S_ISREG(info.st_mode) and info.st_nlink==1,'nonregular or multilink member'
   b=p.read_bytes();files[rel]={'bytes':len(b),'sha256':digest(b),'mode':stat.S_IMODE(info.st_mode)}
 return files,sorted(directories)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('root');ap.add_argument('--final',required=True);ap.add_argument('--manifest',required=True);ap.add_argument('--report',required=True);a=ap.parse_args();root=Path(a.root)
 for name,h in [('FINAL.md',a.final),('MANIFEST.json',a.manifest),('REPORT.md',a.report)]:
  p=root/name;i=p.lstat();assert stat.S_ISREG(i.st_mode) and i.st_nlink==1,'bad envelope'
  assert digest(p.read_bytes())==h,'detached anchor mismatch: '+name
 m=json.loads((root/'MANIFEST.json').read_bytes());assert m['format']=='r169-exact-selection-v1'
 for rel in m['files']:
  p=PurePosixPath(rel);assert not p.is_absolute() and '..' not in p.parts and rel not in ENVELOPES,'unsafe member path'
 actual,dirs=inventory(root);assert actual==m['files'],'payload membership/bytes/hash/mode mismatch';assert dirs==m['directories'],'directory membership mismatch'
 print(json.dumps({'artifact_replay':'matched','files':len(actual),'directories':len(dirs),'mathematical_gate':False}))
if __name__=='__main__':main()
