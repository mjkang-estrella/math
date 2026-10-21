#!/usr/bin/env python3
"""Read-only exact-membership verifier; detached anchors are mandatory."""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(b):return hashlib.sha256(b).hexdigest()
def verify(root,anchors):
 root=Path(root)
 if root.is_symlink() or not root.is_dir():raise ValueError('root is not an ordinary directory')
 root=root.resolve()
 for name in sorted(ENVELOPES):
  p=root/name
  if p.is_symlink() or not p.is_file():raise ValueError('invalid envelope '+name)
  if digest(p.read_bytes())!=anchors[name]:raise ValueError('detached anchor mismatch '+name)
 obj=json.loads((root/'MANIFEST.json').read_bytes())
 if obj.get('schema')!='r151-exact-files-v1':raise ValueError('manifest schema')
 expected={}
 for row in obj['files']:
  rel=row['path'];p=PurePosixPath(rel)
  if p.is_absolute() or '..' in p.parts or str(p)!=rel or rel in ENVELOPES or rel in expected:raise ValueError('invalid manifest path')
  expected[rel]=row
 observed={}
 for dp,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in ds:
   if (Path(dp)/name).is_symlink():raise ValueError('symlink directory')
  for name in fs:
   p=Path(dp)/name;rel=p.relative_to(root).as_posix();st=p.lstat()
   if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('nonordinary file '+rel)
   observed[rel]=p
 if set(observed)!=set(expected)|ENVELOPES:raise ValueError('exact membership mismatch')
 for rel,row in expected.items():
  b=observed[rel].read_bytes()
  if len(b)!=row['size'] or digest(b)!=row['sha256']:raise ValueError('payload mismatch '+rel)
 return {'artifact_verification':'PASS','payload_files':len(expected),'envelopes':3,'scope':'bytes/membership/link checks only; no mathematical gate'}
def main():
 p=argparse.ArgumentParser();p.add_argument('root');p.add_argument('--manifest-sha256',required=True);p.add_argument('--final-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
 try: print(json.dumps(verify(a.root,{'MANIFEST.json':a.manifest_sha256,'FINAL.md':a.final_sha256,'REPORT.md':a.report_sha256}),sort_keys=True))
 except (OSError,ValueError,KeyError,TypeError) as e:print(json.dumps({'artifact_verification':'FAIL','reason':str(e)}));raise SystemExit(1)
if __name__=='__main__':main()
