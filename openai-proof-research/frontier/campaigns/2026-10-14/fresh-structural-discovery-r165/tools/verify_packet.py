"""Read-only byte/membership verifier. Three detached anchors are mandatory."""
import argparse,hashlib,json,os,stat
from pathlib import Path
ENVELOPES=('FINAL.md','MANIFEST.json','REPORT.md')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:
  if k in d:raise ValueError('duplicate JSON key')
  d[k]=v
 return d
def inventory(root):
 files={};dirs={'.':stat.S_IMODE(root.lstat().st_mode)}
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 for cur,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in ds+fs:
   p=Path(cur)/name;s=p.lstat();rel=p.relative_to(root).as_posix()
   if stat.S_ISLNK(s.st_mode):raise ValueError('symlink: '+rel)
   if stat.S_ISDIR(s.st_mode):dirs[rel]=stat.S_IMODE(s.st_mode)
   elif stat.S_ISREG(s.st_mode):
    if s.st_nlink!=1:raise ValueError('non-single link: '+rel)
    files[rel]={'size':s.st_size,'mode':stat.S_IMODE(s.st_mode),'sha256':digest(p)}
   else:raise ValueError('nonregular member: '+rel)
 return files,dirs
def verify(root,anchors):
 root=Path(root)
 for name,anchor in zip(ENVELOPES,anchors):
  p=root/name
  if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):raise ValueError('invalid detached anchor')
  if p.is_symlink() or not p.is_file() or digest(p)!=anchor:raise ValueError('detached mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_text(),object_pairs_hook=unique)
 if m['format']!=1 or m['envelopes']!=list(ENVELOPES):raise ValueError('manifest format')
 files,dirs=inventory(root)
 for name in ENVELOPES:
  if files[name]['mode']!=0o444:raise ValueError('envelope mode')
  del files[name]
 if files!=m['files']:raise ValueError('payload bytes/membership/modes')
 if dirs!=m['directories']:raise ValueError('directory membership/modes')
 if 'tools/verify_packet.py' not in files:raise ValueError('unbound verifier')
 return {'artifact_only':True,'payload_files':len(files),'directories_including_root':len(dirs),'verified':True}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root');p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
 try:print(json.dumps(verify(a.root,[a.final_sha256,a.manifest_sha256,a.report_sha256]),sort_keys=True))
 except Exception as e:print(json.dumps({'verified':False,'error':str(e)}));raise SystemExit(1)
