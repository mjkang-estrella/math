"""Read-only exact-inventory verifier. Supply three detached SHA256 anchors.
This authenticates bytes and file-set membership, never mathematical conclusions.
"""
import argparse,hashlib,json,os,re,stat
from pathlib import Path
ENVELOPES=('envelopes/FINAL.md','envelopes/MANIFEST.json','envelopes/REPORT.md')
def sha(data):return hashlib.sha256(data).hexdigest()
def inventory(root):
 if root.is_symlink() or not root.is_dir():raise ValueError('root is not an ordinary directory')
 files={};dirs=[]
 for here,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in sorted(ds+fs):
   p=Path(here)/name;rel=p.relative_to(root).as_posix();st=p.lstat()
   if stat.S_ISLNK(st.st_mode):raise ValueError('symlink: '+rel)
   if stat.S_ISDIR(st.st_mode):dirs.append(rel)
   elif stat.S_ISREG(st.st_mode):
    if st.st_nlink!=1:raise ValueError('non-single-link file: '+rel)
    if rel not in ENVELOPES:
     b=p.read_bytes();files[rel]={'bytes':len(b),'sha256':sha(b)}
   else:raise ValueError('special entry: '+rel)
 return {'schema':'r132-exact-selection-v1','excludes':list(ENVELOPES),'directories':sorted(dirs),'files':dict(sorted(files.items()))}
def verify(root,anchors):
 actual=inventory(root)
 for rel,anchor in zip(ENVELOPES,anchors):
  if re.fullmatch('[0-9a-f]{64}',anchor) is None:raise ValueError('invalid detached anchor')
  p=root/rel
  if not p.is_file() or p.is_symlink() or p.stat().st_nlink!=1:raise ValueError('invalid envelope: '+rel)
  if sha(p.read_bytes())!=anchor:raise ValueError('detached anchor mismatch: '+rel)
 recorded=json.loads((root/ENVELOPES[1]).read_bytes())
 if recorded!=actual:raise ValueError('exact inventory differs from manifest')
 return len(actual['files'])
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path)
 p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True);a=p.parse_args()
 try:print('Artifact-only inventory verified:',verify(a.root,(a.final,a.manifest,a.report)),'payload files; three detached envelopes')
 except (OSError,ValueError,TypeError) as e:p.exit(1,'Artifact verification failed: '+str(e)+'\n')
