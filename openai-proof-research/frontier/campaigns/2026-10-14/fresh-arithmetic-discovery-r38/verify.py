#!/usr/bin/env python3
"""MIT. Authenticate externally anchored exact inventory and canonical identities.
This never creates or rewrites a seal and does not certify the mathematics.
"""
import hashlib,json,os,stat,sys
from pathlib import Path

def sha(b):return hashlib.sha256(b).hexdigest()
def safe(root,name):
 p=Path(name)
 if p.is_absolute() or '..' in p.parts or p.as_posix()!=name:raise ValueError('unsafe relative path')
 return root/p

def check(expected):
 script=Path(__file__)
 if '..' in script.parts:raise ValueError('parent traversal in invocation')
 if not script.is_absolute():script=Path.cwd()/script
 root=script.parent
 for p in (root,*root.parents):
  if not stat.S_ISDIR(p.lstat().st_mode):raise ValueError('non-directory or symlink ancestor')
 files={};dirs=[]
 def walk(p):
  for entry in os.scandir(p):
   q=Path(entry.path);rel=q.relative_to(root).as_posix();s=q.lstat()
   if stat.S_ISDIR(s.st_mode):dirs.append(rel);walk(q)
   elif stat.S_ISREG(s.st_mode):
    if s.st_nlink!=1:raise ValueError('hardlink: '+rel)
    if q.name=='manifest.json' and rel!='manifest.json':raise ValueError('nested manifest')
    files[rel]={'bytes':s.st_size,'sha256':sha(q.read_bytes())}
   else:raise ValueError('nonregular entry: '+rel)
 walk(root)
 raw=(root/'manifest.json').read_bytes()
 if sha(raw)!=expected:raise ValueError('external manifest anchor mismatch')
 manifest=json.loads(raw)
 if sorted(dirs)!=manifest['directories']:raise ValueError('directory inventory mismatch')
 del files['manifest.json']
 if files!=manifest['files']:raise ValueError('file inventory mismatch')
 ctx=json.loads((root/'context-identities.json').read_text())
 for r in ctx['contexts']:
  b=safe(root,r['copy']).read_bytes()
  if len(b)!=r['bytes'] or sha(b)!=r['sha256']:raise ValueError('context identity mismatch')
 tree=json.loads((root/'private/context/preprints-tree.json').read_text())
 if tree['truncated'] is not False or len(tree['tree'])!=13223:raise ValueError('incomplete canonical tree')
 if sha((root/'private/context/preprints-tree.json').read_bytes())!='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b':raise ValueError('canonical tree anchor mismatch')
 inv=json.loads((root/'source-family-inventory.json').read_text())
 entries=[e for e in tree['tree'] if any(e['path'].startswith(f+'/') for f in ctx['families'])]
 if entries!=inv['entries']:raise ValueError('source family completeness mismatch')
 pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
 if inv['pin']!=pin or json.loads((root/'private/context/upstream.json').read_text())['commit']!=pin:raise ValueError('pin mismatch')
 receipts=json.loads((root/'source205-receipts.json').read_text())
 actual={r['source_path']:r['git_blob'] for r in receipts}
 wanted={r['path']:r['sha'] for r in entries if r['type']=='blob' and (r['path'].endswith('.tex') or r['path'].endswith('/README.md'))}
 if len(receipts)!=len(actual) or actual!=wanted:raise ValueError('selected source completeness mismatch')
 for r in receipts:
  b=safe(root,r['path']).read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  if git!=r['git_blob'] or sha(b)!=r['sha256'] or len(b)!=r['bytes']:raise ValueError('source identity mismatch')
 for r in json.loads((root/'primary-identities.json').read_text()):
  b=safe(root,r['path']).read_bytes();t=safe(root,r['text_path']).read_bytes()
  if sha(b)!=r['sha256'] or len(b)!=r['bytes'] or sha(t)!=r['text_sha256'] or len(t)!=r['text_bytes']:raise ValueError('primary identity mismatch')
 r=json.loads((root/'provenance/parent-copy-receipt.json').read_text())
 if sha(safe(root,r['copy']).read_bytes())!=r['sha256']:raise ValueError('parent copy identity mismatch')
 if sha((root/'scope205m.md').read_bytes())!='3eb9d790999b419a4083ead2a3ed0979217a36a12bdd78ceabe7fa6d3afb64f6':raise ValueError('frozen scope mismatch')
 print(json.dumps({'status':'PASS_EXACT_INVENTORY','files':len(files),'directories':len(dirs),'canonical_tree_entries':len(tree['tree']),'family_entries':len(entries),'selected_source_blobs':len(receipts),'primary_pdfs':4}))
if __name__=='__main__':
 try:
  if len(sys.argv)!=2 or len(sys.argv[1])!=64 or any(c not in '0123456789abcdef' for c in sys.argv[1]):raise ValueError('external SHA256 argument required')
  check(sys.argv[1])
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
