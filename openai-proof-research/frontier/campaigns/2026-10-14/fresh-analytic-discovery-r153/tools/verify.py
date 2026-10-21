#!/usr/bin/env python3
"""Read-only exact-membership verifier. All detached anchors are mandatory."""
import argparse,hashlib,json,os,stat,sys
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def members(root):
 out={}
 for base,dirs,files in os.walk(root,topdown=True,followlinks=False):
  for n in dirs:
   if (Path(base)/n).is_symlink():raise ValueError('symlink directory')
  for n in files:
   p=Path(base)/n;s=p.lstat();rel=p.relative_to(root).as_posix()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('nonregular or multiply linked file: '+rel)
   if rel not in ENVELOPES:out[rel]={'bytes':s.st_size,'sha256':digest(p)}
 return out
def main():
 ap=argparse.ArgumentParser();ap.add_argument('root',type=Path)
 for n in ['final','manifest','report']:ap.add_argument('--'+n+'-sha',required=True)
 a=ap.parse_args();root=a.root.resolve()
 for n,anchor in [('FINAL.md',a.final_sha),('MANIFEST.json',a.manifest_sha),('REPORT.md',a.report_sha)]:
  p=root/n;s=p.lstat()
  if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1 or digest(p)!=anchor:raise ValueError('detached anchor mismatch: '+n)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m['outside_envelopes']!=sorted(ENVELOPES):raise ValueError('envelope declaration')
 wanted={x['path']:{'bytes':x['bytes'],'sha256':x['sha256']} for x in m['files']}
 if len(wanted)!=len(m['files']):raise ValueError('duplicate manifest paths')
 actual=members(root)
 if actual!=wanted:raise ValueError('payload membership or bytes mismatch')
 print(json.dumps({'verified_payload_files':len(actual),'outside_envelopes':3,'read_only':True,'mathematical_gate':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print('REJECT: '+str(e));sys.exit(1)
