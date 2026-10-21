"""Read-only exact membership verification. External anchors are mandatory.
This verifies bytes, not mathematics, rights, historical originals or isolation.
"""
import argparse,hashlib,json,os,re
from pathlib import Path
OUTER={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
 files={};dirs=[]
 for parent,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(parent)/name
   if p.is_symlink():raise ValueError('symlink rejected: '+str(p.relative_to(root)))
  for d in ds:dirs.append(str((Path(parent)/d).relative_to(root)))
  for f in fs:
   p=Path(parent)/f;rel=str(p.relative_to(root))
   if not p.is_file():raise ValueError('nonregular file')
   files[rel]={'size':p.stat().st_size,'sha256':sha(p)}
 return files,sorted(dirs)
def verify(root,anchors):
 if set(anchors)!=OUTER:raise ValueError('three anchors required')
 for name,digest in anchors.items():
  if not re.fullmatch('[0-9a-f]{64}',digest):raise ValueError('invalid anchor')
  if sha(root/name)!=digest:raise ValueError('external anchor mismatch: '+name)
 manifest=json.loads((root/'MANIFEST.json').read_text())
 if manifest.get('format')!='r145-exact-membership-v1':raise ValueError('manifest format')
 expected=manifest['files']
 if any(Path(p).is_absolute() or '..' in Path(p).parts or p in OUTER for p in expected):raise ValueError('bad payload path')
 actual,dirs=inventory(root)
 if set(actual)!=set(expected)|OUTER:raise ValueError('file membership mismatch')
 if dirs!=manifest['directories']:raise ValueError('directory membership mismatch')
 for p,record in expected.items():
  if actual[p]!=record:raise ValueError('payload mismatch: '+p)
 return {'verified_payload_files':len(expected),'verified_directories':len(dirs),'outer_envelopes':3,'meaning':'byte integrity only'}
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('root',type=Path)
 for name in ['final','manifest','report']:parser.add_argument('--'+name+'-sha256',required=True)
 args=parser.parse_args()
 try:print(json.dumps(verify(args.root.resolve(),{'FINAL.md':args.final_sha256,'MANIFEST.json':args.manifest_sha256,'REPORT.md':args.report_sha256}),sort_keys=True))
 except (ValueError,OSError,KeyError,TypeError,json.JSONDecodeError) as e:parser.exit(1,str(e)+'\n')
