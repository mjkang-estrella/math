"""Read-only artifact verification, requiring independent detached SHA256 anchors.
Run from the project root with python3 -B and the three hashes supplied in handoff.
No network, writes, subprocesses, source execution, or mathematical verification.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, re, stat, sys

def digest(b): return hashlib.sha256(b).hexdigest()
def mode(p): return format(stat.S_IMODE(p.lstat().st_mode),'04o')
def regular(p):
 s=p.lstat()
 if not stat.S_ISREG(s.st_mode): raise ValueError('not a regular non-symlink file: '+str(p))
 return p.read_bytes()
def require(ok,msg):
 if not ok: raise ValueError(msg)
def inventory(packet):
 require(packet.is_dir() and not packet.is_symlink(),'packet is not a real directory')
 files={};dirs={'.':mode(packet)}
 for base,children,names in os.walk(packet,topdown=True,followlinks=False):
  base=Path(base)
  for name in children:
   p=base/name;require(stat.S_ISDIR(p.lstat().st_mode),'symlink/special directory: '+str(p))
   dirs[p.relative_to(packet).as_posix()]=mode(p)
  for name in names:
   p=base/name;b=regular(p);rel=p.relative_to(packet).as_posix()
   files[rel]={'path':rel,'bytes':len(b),'mode':mode(p),'sha256':digest(b)}
 return files,dirs

def verify(root,final_sha,manifest_sha,report_sha):
 for h in [final_sha,manifest_sha,report_sha]:require(re.fullmatch('[0-9a-f]{64}',h) is not None,'malformed detached anchor')
 require(root.is_dir() and not root.is_symlink(),'root is not a real directory')
 mb=regular(root/'MANIFEST.json');rb=regular(root/'REPORT.txt')
 require(digest(mb)==manifest_sha,'detached MANIFEST hash mismatch')
 require(digest(rb)==report_sha,'detached outside REPORT hash mismatch')
 require(mode(root/'MANIFEST.json')=='0444' and mode(root/'REPORT.txt')=='0444','outside anchor-bearing file mode mismatch')
 data=json.loads(mb);require(data['format']=='r197-exact-selected-packet-v1','unknown manifest format')
 packet=root/'packet';files,dirs=inventory(packet)
 expected={}
 for x in data['files']:
  p=PurePosixPath(x['path']);require(not p.is_absolute() and '..' not in p.parts and p.as_posix()==x['path'],'unsafe path')
  require(x['path'] not in expected,'duplicate manifest path');expected[x['path']]=x
 require(set(files)==set(expected),'exact file membership mismatch')
 require(dirs=={x['path']:x['mode'] for x in data['directories']},'exact directory membership/modes mismatch')
 for rel,x in expected.items():require(files[rel]==x,'file bytes/hash/mode mismatch: '+rel)
 require(digest(regular(packet/'FINAL.txt'))==final_sha,'detached FINAL hash mismatch')
 if 'STATEMENT.txt' in files:
  freeze=json.loads(regular(packet/'private/freeze-anchor.json'))
  require(files['STATEMENT.txt']['sha256']==freeze['sha256'],'immutable statement anchor mismatch')
  require(files['STATEMENT.txt']['mode']=='0444','immutable statement mode mismatch')
 if 'private/source-authentication.json' in files:
  auth=json.loads(regular(packet/'private/source-authentication.json'))
  tree=json.loads(regular(packet/'private/source-tree.json'))
  require(len(auth)==10 and len(tree)==13,'canonical selection count mismatch')
  blobs={e['path']:e for e in tree if e['type']=='blob'}
  require(set(blobs)=={e['canonical_path'] for e in auth},'canonical blob selection mismatch')
  pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
  prefix='preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/'
  for e in auth:
   require(e['canonical_path'].startswith(prefix),'unexpected canonical family')
   b=regular(packet/e['local_path']);git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
   t=blobs[e['canonical_path']]
   require(git==e['git_blob']==t['sha'],'canonical Git blob mismatch')
   require(len(b)==e['bytes']==t['size'] and digest(b)==e['sha256'],'canonical size/SHA256 mismatch')
   require(e['url']=='https://raw.githubusercontent.com/openai/math/'+pin+'/'+e['canonical_path'],'unpinned canonical URL')
 return {'artifact_verification':'succeeded','files':len(files),'directories':len(dirs),'read_only':True,'mathematical_status':'not assessed'}

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--root',required=True,type=Path);p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
 try:print(json.dumps(verify(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256),sort_keys=True));return 0
 except Exception as e:print(json.dumps({'artifact_verification':'failed','reason':str(e)},sort_keys=True));return 1
if __name__=='__main__':sys.exit(main())
