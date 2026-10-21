# Original r153 read-only verifier, MIT. Explicit detached anchors are required.
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def verify(root,anchors):
 root=Path(root)
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 for name,anchor in anchors.items():
  p=root/name
  if p.is_symlink() or not p.is_file() or p.stat().st_nlink!=1:raise ValueError('envelope type')
  if sha(p.read_bytes())!=anchor:raise ValueError('detached anchor mismatch: '+name)
 manifest=json.loads((root/'MANIFEST.json').read_text())
 if manifest['schema']!='r153-exact-v1':raise ValueError('schema')
 expected={}
 for item in manifest['files']:
  s=item['path'];p=PurePosixPath(s)
  if p.is_absolute() or '..' in p.parts or '.' in p.parts or str(p)!=s or s in ENVELOPES or s in expected:raise ValueError('unsafe or duplicate path')
  expected[s]=item
 actual={};dirs=['.']
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(base)/name;st=p.lstat();rel=p.relative_to(root).as_posix()
   if stat.S_ISLNK(st.st_mode):raise ValueError('symlink')
   if stat.S_ISDIR(st.st_mode):dirs.append(rel)
   elif stat.S_ISREG(st.st_mode):
    if st.st_nlink!=1:raise ValueError('hardlink')
    if rel not in ENVELOPES:actual[rel]={'bytes':st.st_size,'sha256':sha(p.read_bytes())}
   else:raise ValueError('nonregular object')
 if set(actual)!=set(expected):raise ValueError('file membership mismatch')
 if sorted(dirs)!=manifest['directories']:raise ValueError('directory membership mismatch')
 for s,d in actual.items():
  if d!={k:expected[s][k] for k in ['bytes','sha256']}:raise ValueError('payload mismatch: '+s)
 return {'payload_files':len(actual),'directories':len(dirs),'outside_envelopes':3}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root');p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True);a=p.parse_args()
 try:print(json.dumps(verify(a.root,{'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.md':a.report}),sort_keys=True))
 except Exception as e:raise SystemExit('INVALID: '+str(e))
