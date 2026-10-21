"""Read-only exact-membership verifier. Supply three detached SHA256 anchors."""
import argparse,hashlib,json,os,re,stat,sys
from pathlib import Path

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
 files={};dirs=[]
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in ds:
   p=Path(base)/name;s=p.lstat()
   if not stat.S_ISDIR(s.st_mode) or p.is_symlink():raise ValueError('nonregular directory: '+str(p))
   dirs.append(p.relative_to(root).as_posix())
  for name in fs:
   p=Path(base)/name;s=p.lstat()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('not a single-link regular file: '+str(p))
   files[p.relative_to(root).as_posix()]={'size':s.st_size,'sha256':digest(p)}
 return files,sorted(dirs)
def verify(root,anchors):
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
 for name,expected in anchors.items():
  if not re.fullmatch('[0-9a-f]{64}',expected):raise ValueError('bad detached anchor format')
  p=root/name;s=p.lstat()
  if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1 or digest(p)!=expected:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m['schema']!='r121-packet-only-v1':raise ValueError('wrong manifest schema')
 expected={}
 for x in m['files']:
  p=x['path'];parts=Path(p).parts
  if not p.startswith('packet/') or Path(p).is_absolute() or '..' in parts or p in expected:raise ValueError('invalid payload path')
  expected[p]={'size':x['size'],'sha256':x['sha256']}
 actual,dirs=inventory(root)
 if set(actual)!=set(expected)|set(anchors):raise ValueError('exact file membership mismatch')
 if dirs!=m['directories']:raise ValueError('exact directory membership mismatch')
 if any(actual[p]!=x for p,x in expected.items()):raise ValueError('payload byte mismatch')
 return {'payload_files':len(expected),'outside_envelopes':3,'total_files':len(actual),'directories':len(dirs)}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('root',type=Path)
 for x in ('final','manifest','report'):ap.add_argument('--'+x+'-sha256',required=True)
 a=ap.parse_args()
 try:
  r=verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256});print(json.dumps({'artifact_verification':'PASS',**r}))
 except Exception as e:print('ARTIFACT FAIL: '+str(e));sys.exit(1)
