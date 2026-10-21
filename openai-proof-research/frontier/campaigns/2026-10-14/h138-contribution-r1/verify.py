"""Read-only exact-inventory verifier. Requires THREE externally supplied SHA256s.
No writes, subprocesses, network, execution of packet code, repair or mathematics.
Use python -B. A reduced incoming copy is not the original author root.
"""
import argparse,hashlib,json,os,re
from pathlib import Path,PurePosixPath
ENVELOPES={'MANIFEST.json','REPORT.md','FINAL.json'}
PEER=re.compile(r'h138[-_]|t185r144|structural.*r144|arithmetic.*r10[89]|arithmetic.*r110',re.I)
def digest(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 root=Path(root)
 if root.is_symlink() or not root.is_dir():raise ValueError('ordinary directory required')
 files={};dirs=[]
 for base,ds,ns in os.walk(root,topdown=True,followlinks=False):
  ds.sort();ns.sort()
  # Reject before descent or file-body read. The owned root basename is not a peer.
  for n in ds+ns:
   p=Path(base)/n
   if PEER.search(n):raise ValueError('peer/prohibited component')
   if p.is_symlink():raise ValueError('symlink rejected')
  for n in ds:dirs.append((Path(base)/n).relative_to(root).as_posix())
  for n in ns:
   p=Path(base)/n;rel=p.relative_to(root).as_posix()
   if not p.is_file():raise ValueError('nonregular file')
   if rel in ENVELOPES:continue
   b=p.read_bytes();files[rel]={'size':len(b),'sha256':digest(b)}
 return dict(sorted(files.items())),sorted(dirs)
def verify(root,anchors):
 root=Path(root)
 if root.is_symlink() or not root.is_dir():raise ValueError('ordinary root required')
 for n in sorted(ENVELOPES):
  h=anchors.get(n,'')
  if not re.fullmatch(r'[0-9a-f]{64}',h):raise ValueError('explicit detached anchor required')
  p=root/n
  if p.is_symlink() or not p.is_file():raise ValueError('missing or nonregular envelope')
  if digest(p.read_bytes())!=h:raise ValueError('detached anchor mismatch: '+n)
 m=json.loads((root/'MANIFEST.json').read_text());f=json.loads((root/'FINAL.json').read_text())
 if m.get('schema')!=1 or f.get('schema')!=1:raise ValueError('unknown schema')
 if f.get('manifest_sha256')!=anchors['MANIFEST.json'] or f.get('report_sha256')!=anchors['REPORT.md']:raise ValueError('envelope binding mismatch')
 for n in m['files']:
  q=PurePosixPath(n)
  if q.is_absolute() or '..' in q.parts or q.as_posix()!=n or n in ENVELOPES:raise ValueError('unsafe manifest membership')
 files,dirs=inventory(root)
 if files!=m['files'] or dirs!=m['directories']:raise ValueError('exact payload/directory inventory mismatch')
 return {'integrity':'verified','payload_files':len(files),'payload_directories':len(dirs),'mathematical_gate':False}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',default=str(Path(__file__).resolve().parent));p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True);p.add_argument('--final-sha256',required=True);a=p.parse_args()
 try:print(json.dumps(verify(a.root,{'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256,'FINAL.json':a.final_sha256}),sort_keys=True))
 except (OSError,ValueError,KeyError,TypeError,json.JSONDecodeError) as e:p.exit(1,'Integrity verification rejected: '+str(e)+'\n')
