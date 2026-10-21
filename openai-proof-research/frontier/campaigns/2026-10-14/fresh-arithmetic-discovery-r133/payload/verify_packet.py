"""Read-only artifact checker. Supply all three detached envelope SHA256 anchors.
No network, subprocesses, imports of packet code, or filesystem writes.
This authenticates bytes/membership only; it does not assess mathematics.
"""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath
ENVELOPES=('FINAL.md','MANIFEST.json','REPORT.md')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(payload):
 files={};dirs=[]
 assert not payload.is_symlink() and payload.is_dir(),'payload must be a real directory'
 for current,children,names in os.walk(payload,followlinks=False):
  children.sort();names.sort()
  for name in children+names:
   p=Path(current)/name; mode=p.lstat().st_mode
   relative=p.relative_to(payload).as_posix()
   assert not stat.S_ISLNK(mode),'symlink forbidden: '+relative
   if stat.S_ISDIR(mode): dirs.append(relative)
   else:
    assert stat.S_ISREG(mode),'nonregular entry: '+relative
    files[relative]={'size':p.stat().st_size,'sha256':digest(p)}
 return dict(sorted(files.items())),sorted(dirs)
def verify(root,anchors):
 assert not root.is_symlink() and root.is_dir(),'root must be a real directory'
 assert {p.name for p in root.iterdir()}==set(ENVELOPES)|{'payload'},'outside-envelope membership mismatch'
 assert set(anchors)==set(ENVELOPES),'three detached anchors required'
 for name in ENVELOPES:
  p=root/name
  assert not p.is_symlink() and p.is_file(),'nonregular envelope: '+name
  anchor=anchors[name]
  assert len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor),'invalid anchor'
  assert digest(p)==anchor,'envelope hash mismatch: '+name
 m=json.loads((root/'MANIFEST.json').read_text())
 assert set(m)=={'schema','payload_root','files','directories'},'unexpected manifest fields'
 assert m['schema']=='r133-exact-membership-v1' and m['payload_root']=='payload','wrong schema/root'
 for path in list(m['files'])+m['directories']:
  q=PurePosixPath(path)
  assert not q.is_absolute() and path==q.as_posix() and '..' not in q.parts and path not in ('','.'),'noncanonical member'
 files,dirs=inventory(root/'payload')
 assert files==m['files'],'payload file membership/size/hash mismatch'
 assert dirs==m['directories'],'payload directory membership mismatch'
 return {'files':len(files),'directories':len(dirs),'meaning':'artifact bytes and exact selected membership only'}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('root',type=Path)
 p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True)
 args=p.parse_args()
 print(json.dumps(verify(args.root,dict(zip(ENVELOPES,[args.final,args.manifest,args.report]))),indent=2))
