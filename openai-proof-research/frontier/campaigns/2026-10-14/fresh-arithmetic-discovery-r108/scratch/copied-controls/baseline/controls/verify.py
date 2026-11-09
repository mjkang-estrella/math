"""Read-only exact inventory verifier. Detached anchors must be supplied by caller."""
import argparse,fnmatch,hashlib,json,os,re,sys
from pathlib import Path
OUTSIDE={'MANIFEST.json','FINAL.md','REPORT.md','SHA256SUMS','detached-anchors.json'}
OMIT='scratch/copied-controls'
PATTERNS=['*analytic*r138*','*structural*r144*','*analytic*r137*','t177c143-*','*structural*r143*','t373e135-*','*analytic*r135*','*analytic*r136*','k369r134-*','t088p133-*']
def sha(b): return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={}
 for dp,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for d in list(ds):
   q=Path(dp)/d;rel=q.relative_to(root).as_posix()
   if any(fnmatch.fnmatch(d.lower(),p) for p in PATTERNS): raise ValueError('excluded component present: '+rel)
   if q.is_symlink(): raise ValueError('symlink: '+rel)
   if rel==OMIT: ds.remove(d)
  for f in fs:
   q=Path(dp)/f;rel=q.relative_to(root).as_posix()
   if any(fnmatch.fnmatch(f.lower(),p) for p in PATTERNS): raise ValueError('excluded filename present: '+rel)
   if q.is_symlink() or not q.is_file(): raise ValueError('nonregular file: '+rel)
   if rel in OUTSIDE: continue
   b=q.read_bytes();files[rel]={'bytes':len(b),'sha256':sha(b)}
 return files

def verify(root,anchors):
 if root.is_symlink(): raise ValueError('root symlink')
 root=root.resolve()
 for name,h in anchors.items():
  if not re.fullmatch('[0-9a-f]{64}',h): raise ValueError('invalid anchor format')
  p=root/name
  if p.is_symlink() or sha(p.read_bytes())!=h: raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m['format']!='r108-exact-v1' or m['outside_files']!=sorted(OUTSIDE) or m['omitted_subtree']!=OMIT: raise ValueError('inventory policy mismatch')
 if inventory(root)!=m['files']: raise ValueError('payload inventory/hash mismatch')
 return {'status':'artifact-integrity-only','files':len(m['files']),'detached_anchors':anchors,'mathematical_gate':False}

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
 for flag in ['manifest','final','report']: p.add_argument('--'+flag+'-sha',required=True)
 a=p.parse_args();anchors={'MANIFEST.json':a.manifest_sha,'FINAL.md':a.final_sha,'REPORT.md':a.report_sha}
 try: result=verify(a.root,anchors)
 except Exception as e: print(type(e).__name__+': '+str(e),file=sys.stderr);return 1
 print(json.dumps(result,indent=2));return 0
if __name__=='__main__': sys.exit(main())
