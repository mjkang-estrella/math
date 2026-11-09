#!/usr/bin/env python3
"""Read-only integrity verification; requires three externally supplied anchors."""
import argparse,hashlib,json,os
from pathlib import Path,PurePosixPath
ENVELOPES={'MANIFEST.json','FINAL.json','REPORT.md','SHA256SUMS'}
def sha(data):return hashlib.sha256(data).hexdigest()
def check(root,anchors):
 root=Path(root).absolute()
 assert root.is_dir() and not root.is_symlink(),'invalid root'
 for name,digest in anchors.items():
  assert len(digest)==64 and all(c in '0123456789abcdef' for c in digest),'invalid anchor'
  p=root/name
  assert p.is_file() and not p.is_symlink(),name
  assert sha(p.read_bytes())==digest,'anchor mismatch: '+name
 manifest=json.loads((root/'MANIFEST.json').read_text())
 final=json.loads((root/'FINAL.json').read_text())
 assert manifest['format']=='r143-exact-files-v1'
 assert final['manifest_sha256']==anchors['MANIFEST.json']
 assert final['report_sha256']==anchors['REPORT.md']
 paths=set()
 for row in manifest['files']:
  name=row['path'];p=PurePosixPath(name)
  assert name and not p.is_absolute() and '..' not in p.parts and str(p)==name
  assert name not in paths and name not in ENVELOPES,'duplicate/envelope'
  paths.add(name)
  target=root/name
  assert target.is_file() and not target.is_symlink(),'missing/nonfile: '+name
  data=target.read_bytes()
  assert len(data)==row['bytes'] and sha(data)==row['sha256'],'payload mismatch: '+name
 actual=set()
 for d,ds,fs in os.walk(root,followlinks=False):
  for s in ds+fs:assert not (Path(d)/s).is_symlink(),'symlink'
  for f in fs:actual.add((Path(d)/f).relative_to(root).as_posix())
 assert actual==paths|ENVELOPES,'file membership mismatch'
 v=final['verifier_path']
 assert v in paths and sha((root/v).read_bytes())==final['verifier_sha256']
 expected=''.join(anchors[name]+'  '+name+'\n' for name in ['FINAL.json','MANIFEST.json','REPORT.md'])
 assert (root/'SHA256SUMS').read_text()==expected,'detached-list mismatch'
 return len(paths)
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('root');p.add_argument('--manifest-sha256',required=True)
 p.add_argument('--final-sha256',required=True);p.add_argument('--report-sha256',required=True)
 a=p.parse_args()
 try:
  n=check(a.root,{'MANIFEST.json':a.manifest_sha256,'FINAL.json':a.final_sha256,'REPORT.md':a.report_sha256})
 except (AssertionError,ValueError,OSError,KeyError,TypeError) as e:
  print('FAIL:',str(e));return 1
 print('OK: exact membership and hashes for',n,'payload files; no mathematical grade.');return 0
if __name__=='__main__':raise SystemExit(main())
