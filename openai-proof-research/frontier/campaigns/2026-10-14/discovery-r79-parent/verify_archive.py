#!/usr/bin/env python3
"""Parent external-anchor wrapper for r79 public archive; identity only, MIT."""
import argparse,hashlib,json,os,stat,subprocess,sys
from pathlib import Path

def verify(packet,anchor,repo):
 if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):raise ValueError('malformed anchor')
 if any(p.is_symlink() for p in (packet,*packet.parents)):raise ValueError('symlink ancestry')
 raw=(packet/'MANIFEST.json').read_bytes()
 if hashlib.sha256(raw).hexdigest()!=anchor:raise ValueError('external anchor mismatch')
 m=json.loads(raw);public={}
 for root,dirs,files in os.walk(packet):
  for n in dirs+files:
   p=Path(root)/n;r=p.relative_to(packet);s=p.lstat()
   if stat.S_ISLNK(s.st_mode):raise ValueError('symlink entry')
   if not(stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode)):raise ValueError('nonregular entry')
   if stat.S_ISREG(s.st_mode) and s.st_nlink!=1:raise ValueError('hardlink entry')
   if r.parts[0]=='private':continue
   if stat.S_ISDIR(s.st_mode):raise ValueError('extra public directory')
   if str(r)!='MANIFEST.json':
    b=p.read_bytes();public[str(r)]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if public!=m['files']:raise ValueError('public inventory mismatch')
 r=subprocess.run([sys.executable,'-B',str(packet/'verify_checkpoint.py'),'--repo',str(repo)],capture_output=True,text=True)
 if r.returncode:raise ValueError(r.stderr)
 return {'external_anchor':anchor,'public_inventory_checked':True,'author_identity':json.loads(r.stdout),'mathematics_certified':False,'private_inventory_sealed':False}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--packet',type=Path,required=True);p.add_argument('--anchor',required=True);p.add_argument('--repo',type=Path,required=True);a=p.parse_args()
 try:print(json.dumps(verify(a.packet.absolute(),a.anchor,a.repo.absolute()),sort_keys=True))
 except Exception as e:raise SystemExit('REFUSED: '+str(e))
