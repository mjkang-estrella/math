#!/usr/bin/env python3
# MIT. Read-only identity verifier. Requires externally obtained full anchors.
import argparse,hashlib,json,re,stat
from pathlib import Path
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
SCOPE='0b57f7972d43586f721a6e1aaa42cdd6fa8c80512702f933796b82e2bcd3f6ef'
PROOF='fe18edab356729afe1c0cd96919bf20210ac7ba72c756a125495113d3f78e0ff'
def sha(b):return hashlib.sha256(b).hexdigest()
def checked(p,want):
 if p.is_symlink() or not stat.S_ISREG(p.lstat().st_mode):raise ValueError('nonregular file: '+str(p))
 b=p.read_bytes()
 if sha(b)!=want:raise ValueError('SHA256 mismatch: '+str(p))
 return b
def inventory(root):
 rows=[]
 for name in ['packet','work']:
  p=root/name
  if p.is_symlink() or not p.is_dir():raise ValueError('bad payload root')
  for q in [p,*sorted(p.rglob('*'))]:
   s=q.lstat();rel=q.relative_to(root).as_posix()
   if stat.S_ISLNK(s.st_mode):raise ValueError('payload symlink')
   if stat.S_ISDIR(s.st_mode):rows.append({'path':rel,'kind':'directory'})
   elif stat.S_ISREG(s.st_mode):
    b=q.read_bytes();rows.append({'path':rel,'kind':'file','size':len(b),'sha256':sha(b)})
   else:raise ValueError('nonregular payload entry')
 return sorted(rows,key=lambda x:x['path'])
def verify(root,ma,ra,fa):
 for a in [ma,ra,fa]:
  if not re.fullmatch('[0-9a-f]{64}',a):raise ValueError('complete external SHA256 required')
 m=json.loads(checked(root/'MANIFEST.json',ma));checked(root/'outsideREPORT.md',ra);f=json.loads(checked(root/'FINAL.json',fa))
 if m['entries']!=inventory(root):raise ValueError('exact payload inventory mismatch')
 if f['manifest_sha256']!=ma or f['outside_report_sha256']!=ra:raise ValueError('FINAL binding mismatch')
 if f['verdict']!='TECHNICAL' or f['conditional_on_correctness'] is not True:raise ValueError('verdict binding mismatch')
 inp=root/'packet/private/inputs'
 checked(inp/'author/frozen-scope.md',SCOPE);checked(inp/'author/author-proof.md',PROOF)
 tree=json.loads(checked(inp/'context/sources/preprints-tree.json',TREE))
 if tree['truncated'] or len(tree['tree'])!=13223:raise ValueError('wrong pinned tree')
 by={e['path']:e for e in tree['tree']}
 auth=json.loads((inp/'pinned-sources/authentication.json').read_text())
 for a in auth:
  p=Path(a['path'])
  if p.is_absolute() or '..' in p.parts:raise ValueError('unsafe source path')
  b=checked(inp/'pinned-sources'/p,a['sha256']);e=by[a['path']]
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  if len(b)!=e['size'] or blob!=e['sha'] or blob!=a['git_blob_sha1']:raise ValueError('source Gitblob mismatch')
 for folder in [inp/'retained-primary',root/'packet/private/primary']:
  for a in json.loads((folder/'acquisition.json').read_text()):
   if a.get('status')=='acquisition failed':continue
   checked(folder/(a['name']+'.pdf'),a['sha256']);checked(folder/(a['name']+'.txt'),a['text_sha256'])
 for a in json.loads((root/'packet/private/input-bindings.json').read_text()):
  p=Path(a['copy'])
  if p.is_absolute() or '..' in p.parts:raise ValueError('unsafe input path')
  checked(root/p,a['sha256'])
 return {'status':'ARTIFACT_IDENTITIES_ONLY','verdict_binding':'TECHNICAL_CONDITIONAL','pinned_blobs':len(auth),'payload_entries':len(m['entries']),'mathematical_correctness_gate':False}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
 for name in ['manifest','report','final']:p.add_argument('--'+name+'-sha256',required=True)
 a=p.parse_args()
 try:print(json.dumps(verify(a.root.resolve(),a.manifest_sha256,a.report_sha256,a.final_sha256),sort_keys=True))
 except Exception as e:raise SystemExit('VERIFY FAILED: '+str(e))
