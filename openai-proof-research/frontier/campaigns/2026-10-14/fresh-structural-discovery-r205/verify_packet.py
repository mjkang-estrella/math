"""Read-only exact-selection verifier. Detached anchors MUST be supplied explicitly.
Checks artifact bytes and modes only; does not assess mathematics.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,os,stat,sys

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(root,final_sha,manifest_sha,report_sha):
 root=Path(root)
 for name,digest in [('FINAL.md',final_sha),('MANIFEST.json',manifest_sha),('REPORT.md',report_sha)]:
  p=root/name
  if p.is_symlink() or not p.is_file() or sha(p)!=digest:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m['schema']!='r205-exact-selection-v1':raise ValueError('schema')
 expected={}
 for e in m['files']:
  rel=e['path'];q=PurePosixPath(rel)
  if q.is_absolute() or '..' in q.parts or str(q)!=rel or rel in expected:raise ValueError('invalid/duplicate selected path')
  expected[rel]=e;p=root/rel
  if p.is_symlink() or not p.is_file():raise ValueError('missing/nonregular selected file: '+rel)
  if p.stat().st_size!=e['bytes'] or sha(p)!=e['sha256']:raise ValueError('content mismatch: '+rel)
  if format(stat.S_IMODE(p.stat().st_mode),'04o')!=e['mode']:raise ValueError('mode mismatch: '+rel)
 if 'FINAL.md' not in expected:raise ValueError('FINAL not selected')
 for rel,mode in m['directories'].items():
  p=root if rel=='.' else root/rel
  if p.is_symlink() or not p.is_dir() or format(stat.S_IMODE(p.stat().st_mode),'04o')!=mode:raise ValueError('directory mode/type mismatch: '+rel)
 outside=set(m['outside_files']);skip=set(m['outside_directories']);actual=set()
 for base,dirs,files in os.walk(root,followlinks=False):
  base=Path(base)
  for d in list(dirs):
   x=base/d;rel=x.relative_to(root).as_posix()
   if x.is_symlink():raise ValueError('directory symlink: '+rel)
   if rel in skip:dirs.remove(d)
   elif rel not in m['directories']:raise ValueError('unexpected directory: '+rel)
  for f in files:
   x=base/f;rel=x.relative_to(root).as_posix()
   if x.is_symlink():raise ValueError('file symlink: '+rel)
   if rel not in outside:actual.add(rel)
 if actual!=set(expected):raise ValueError('selection mismatch: '+repr(sorted(actual^set(expected))))
 return {'artifact_checks':'passed','selected_files':len(expected),'selected_bytes':sum(e['bytes'] for e in expected.values()),'explicit_detached_anchors':True,'mathematical_gate':False}

if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--root',required=True);a.add_argument('--final-sha256',required=True);a.add_argument('--manifest-sha256',required=True);a.add_argument('--report-sha256',required=True);n=a.parse_args()
 try:print(json.dumps(verify(n.root,n.final_sha256,n.manifest_sha256,n.report_sha256),sort_keys=True))
 except Exception as e:print(str(e),file=sys.stderr);sys.exit(1)
