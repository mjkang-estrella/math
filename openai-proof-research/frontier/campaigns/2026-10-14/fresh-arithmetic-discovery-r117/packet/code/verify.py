#!/usr/bin/env python3
"""Read-only exact-membership verifier; independent detached anchors are REQUIRED.
Checks byte integrity only, not mathematical truth, rights, or initial-read identity.
"""
import argparse,hashlib,json,os,stat
from pathlib import Path

def digest(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={};dirs=[]
 def visit(p):
  with os.scandir(p) as it:
   for e in sorted(it,key=lambda z:z.name):
    q=Path(e.path);rel=q.relative_to(root).as_posix();s=e.stat(follow_symlinks=False)
    if stat.S_ISLNK(s.st_mode):raise ValueError('symlink:'+rel)
    if stat.S_ISDIR(s.st_mode):dirs.append(rel);visit(q)
    elif stat.S_ISREG(s.st_mode):
     if s.st_nlink!=1:raise ValueError('hardlink:'+rel)
     b=q.read_bytes();files[rel]={'size':len(b),'sha256':digest(b)}
    else:raise ValueError('nonregular:'+rel)
 visit(root);return files,sorted(dirs)

def verify(root,anchors):
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
 files,dirs=inventory(root)
 for n,h in anchors.items():
  if n not in files or files[n]['sha256']!=h:raise ValueError('external anchor mismatch:'+n)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m['format']!='r117-exact-v1':raise ValueError('format')
 expected=dict(m['payload_files']);expected.update(m['envelopes']);expected['MANIFEST.json']=files['MANIFEST.json']
 if files!=expected:raise ValueError('exact file membership/hash mismatch')
 if dirs!=m['directories']:raise ValueError('exact directory membership mismatch')
 return {'ok':True,'payload_files':len(m['payload_files']),'whole_files':len(files),'directories':len(dirs),'read_only':'no write operations; independently snapshot tested','scope':'bytes/membership only; modes not bound'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root');p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
 try: print(json.dumps(verify(Path(a.root),{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}),sort_keys=True))
 except Exception as e:print(json.dumps({'ok':False,'error':str(e)}));raise SystemExit(1)
