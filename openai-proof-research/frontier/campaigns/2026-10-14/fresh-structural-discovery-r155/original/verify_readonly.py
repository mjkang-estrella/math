"""Read-only byte/membership verifier; no mathematical/provenance verdict."""
from pathlib import Path
import os,stat,json,hashlib,argparse
ENVELOPES=('FINAL.md','MANIFEST.json','REPORT.md')
def digest(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 assert stat.S_ISDIR(root.lstat().st_mode) and not root.is_symlink(),'bad root'
 files=[];dirs=['.']
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in ds:
   p=Path(base)/name;s=p.lstat();assert stat.S_ISDIR(s.st_mode) and not p.is_symlink(),'bad directory'
   dirs.append(p.relative_to(root).as_posix())
  for name in fs:
   p=Path(base)/name;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1,'bad file type/link'
   rel=p.relative_to(root).as_posix()
   if rel not in ENVELOPES:
    b=p.read_bytes();files.append({'path':rel,'size':len(b),'sha256':digest(b)})
 return {'version':1,'directories':sorted(dirs),'files':sorted(files,key=lambda x:x['path'])}
def main():
 a=argparse.ArgumentParser();a.add_argument('root');a.add_argument('--final',required=True);a.add_argument('--manifest',required=True);a.add_argument('--report',required=True);x=a.parse_args();r=Path(x.root).absolute()
 for name,anchor in zip(ENVELOPES,(x.final,x.manifest,x.report)):
  assert len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor),'malformed anchor'
  p=r/name;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1,'bad envelope'
  assert digest(p.read_bytes())==anchor,'outside anchor mismatch: '+name
 m=json.loads((r/'MANIFEST.json').read_bytes());actual=inventory(r);assert m==actual,'exact payload membership/content mismatch'
 print(json.dumps({'byte_integrity':'matched','payload_files':len(actual['files']),'directories':len(actual['directories']),'mathematical_gate':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:raise SystemExit('REJECTED: '+str(e))
