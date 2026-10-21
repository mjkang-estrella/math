"""Read-only verifier. Supply detached anchors; never rewrites a packet."""
from pathlib import Path
import argparse,hashlib,json,os,re,stat
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
 files={};dirs=[]
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in sorted(ds+fs):
   p=Path(base)/name;st=p.lstat();rel=p.relative_to(root).as_posix()
   if stat.S_ISDIR(st.st_mode):dirs.append(rel)
   elif stat.S_ISREG(st.st_mode) and st.st_nlink==1:
    b=p.read_bytes();files[rel]={'bytes':len(b),'sha256':digest(b)}
   else:raise ValueError('nonregular/symlink/multilink: '+rel)
 return dict(sorted(files.items())),sorted(dirs)
def verify(root,anchors):
 for name in ENVELOPES:
  val=anchors[name]
  if not re.fullmatch('[0-9a-f]{64}',val):raise ValueError('invalid detached anchor')
  p=root/name;st=p.lstat()
  if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('bad envelope type')
  if digest(p.read_bytes())!=val:raise ValueError('envelope anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m.get('format')!='r159-exact-payload-v1' or set(m.get('outside_envelopes',[]))!=ENVELOPES:raise ValueError('manifest format')
 files,dirs=inventory(root)
 payload={k:v for k,v in files.items() if k not in ENVELOPES}
 if payload!=m.get('files') or dirs!=m.get('directories'):raise ValueError('payload membership/identity mismatch')
 return {'verified_payload_files':len(payload),'verified_directories':len(dirs),'outside_envelopes':3,'read_only':True,'mathematical_gate':False}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root');p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True);a=p.parse_args()
 try:print(json.dumps(verify(Path(a.root),{'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.md':a.report}),sort_keys=True))
 except Exception as e:print('REJECT: '+str(e));raise SystemExit(1)
