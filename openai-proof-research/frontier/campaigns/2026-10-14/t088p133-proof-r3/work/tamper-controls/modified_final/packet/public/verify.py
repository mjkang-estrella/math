#!/usr/bin/env python3
"""MIT. Read-only integrity verifier. Supply three independent detached anchors.
No mathematical claim is proved by this verifier. Private bodies keep original rights.
"""
import argparse,hashlib,json,stat,sys
from pathlib import Path
sys.dont_write_bytecode=True

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
 if not ok:raise ValueError(msg)
def safe_file(root,rel):
 p=Path(rel)
 require(not p.is_absolute() and '..' not in p.parts,'unsafe manifest path')
 q=root/p
 require(q.is_file() and not q.is_symlink(),'missing or linked file: '+rel)
 return q

def verify(root,final_anchor,manifest_anchor,report_anchor,originals=None):
 root=Path(root)
 for rel,h in [('FINAL.json',final_anchor),('packet/MANIFEST.json',manifest_anchor),('REPORT.md',report_anchor)]:
  require(len(h)==64 and all(c in '0123456789abcdef' for c in h),'invalid external anchor')
  require(digest(safe_file(root,rel))==h,'detached anchor mismatch: '+rel)
 final=json.loads((root/'FINAL.json').read_text());manifest=json.loads((root/'packet/MANIFEST.json').read_text())
 require(final['manifest_sha256']==manifest_anchor,'FINAL manifest binding')
 require(final['outside_report_sha256']==report_anchor,'FINAL report binding')
 require(final['verdict']=='PASS_FULL_T088P133','unexpected final verdict')
 observed_files=set();observed_dirs=set()
 for p in (root/'packet').rglob('*'):
  require(not p.is_symlink(),'linked packet object')
  rel=str(p.relative_to(root))
  if p.is_file():observed_files.add(rel)
  elif p.is_dir():observed_dirs.add(rel)
  else:raise ValueError('special packet object')
 observed_files.discard('packet/MANIFEST.json')
 require(observed_files==set(manifest['files']),'packet file layout mismatch')
 require(observed_dirs==set(manifest['directories']),'packet directory layout mismatch')
 for rel,m in manifest['files'].items():
  p=safe_file(root,rel)
  require(p.stat().st_size==m['bytes'] and digest(p)==m['sha256'],'payload mismatch: '+rel)
 for key,rel in [('review_sha256','packet/public/review.md'),('verdict_sha256','packet/public/verdict.json')]:
  require(final[key]==digest(root/rel),'FINAL '+key)
 result={'packet':'PASS','payload_files':len(manifest['files']),'external_detached_anchors':'PASS','mathematical_verdict_in_payload':final['verdict'],'actual_originals':'NOT_CHECKED'}
 if originals is not None:
  base=Path(originals);bindings=json.loads((root/'packet/private/original-bindings-start.json').read_text())
  end=json.loads((root/'packet/private/original-bindings-end.json').read_text())
  require(bindings==end,'start/end original bindings differ')
  for rel,m in bindings.items():
   p=base/rel;s=p.lstat();require(not p.is_symlink(),'linked original')
   d={'type':'dir' if p.is_dir() else 'file','mode':stat.S_IMODE(s.st_mode)}
   if p.is_file():d.update(bytes=s.st_size,sha256=digest(p),nlink=s.st_nlink)
   require(d==m,'actual original changed: '+rel)
  for rel in ['fresh-analytic-discovery-r133','t088p133-proof-r1','t088p133-proof-r2']:
   prefix='frontier/campaigns/2026-10-14/'+rel
   actual={str(p.relative_to(base)) for p in (base/prefix).rglob('*')}|{prefix}
   expected={p for p in bindings if p==prefix or p.startswith(prefix+'/')}
   require(actual==expected,'actual original layout changed: '+prefix)
  result['actual_originals']='PASS';result['bound_original_paths']=len(bindings)
 return result

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[2])
 p.add_argument('--final-sha',required=True);p.add_argument('--manifest-sha',required=True);p.add_argument('--report-sha',required=True)
 p.add_argument('--originals-root',type=Path)
 a=p.parse_args()
 try:print(json.dumps(verify(a.root,a.final_sha,a.manifest_sha,a.report_sha,a.originals_root),indent=2))
 except (ValueError,KeyError,OSError,json.JSONDecodeError) as e:print('FAIL:',e,file=sys.stderr);return 1
 return 0
if __name__=='__main__':sys.exit(main())
