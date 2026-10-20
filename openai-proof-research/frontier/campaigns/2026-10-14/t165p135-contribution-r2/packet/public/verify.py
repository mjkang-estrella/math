#!/usr/bin/env python3
"""MIT. Read-only review artifact verifier. Supply all three DETACHED hashes.
No mathematical verdict is inferred from successful verification.
"""
import argparse,hashlib,json,os,re,stat,sys
from pathlib import Path
SPECIAL={'FINAL.json','REPORT.md','packet/MANIFEST.json'}
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def desc(p):
 s=p.lstat();out={'mode':stat.S_IMODE(s.st_mode)}
 if stat.S_ISLNK(s.st_mode):raise ValueError('symlink: '+p.name)
 if stat.S_ISDIR(s.st_mode):out['type']='directory'
 elif stat.S_ISREG(s.st_mode):
  if s.st_nlink!=1:raise ValueError('hardlink: '+p.name)
  out.update(type='file',nlink=s.st_nlink,size=s.st_size,sha256=digest(p))
 else:raise ValueError('special file: '+p.name)
 return out

def scan(root):
 out={'.':desc(root)}
 for parent,dirs,files in os.walk(root,followlinks=False):
  for name in dirs+files:
   p=Path(parent)/name;rel=p.relative_to(root).as_posix();d=desc(p)
   if rel not in SPECIAL:out[rel]=d
 return out

def verify(root,project,anchors):
 if root.is_symlink():raise ValueError('symlink root')
 for name,h in anchors.items():
  if not re.fullmatch('[a-f0-9]{64}',h):raise ValueError('malformed detached anchor')
  d=desc(root/name)
  if d['mode']!=0o644:raise ValueError('anchor file mode: '+name)
  if d['sha256']!=h:raise ValueError('detached anchor mismatch: '+name)
 final=json.loads((root/'FINAL.json').read_text());m=json.loads((root/'packet/MANIFEST.json').read_text())
 assert final['verdict']=='TECHNICAL' and final['conditional_on_correctness'] is True
 assert final['candidate']=='T165P135' and final['pin']==PIN
 assert final['scope_sha256']=='1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d'
 assert final['proof_sha256']=='a12854336cc118cc9a49dd96bb72aeb142e618ab3466a2e1dc648ff77bf98f10'
 assert final['manifest_sha256']==anchors['packet/MANIFEST.json']
 assert final['report_sha256']==anchors['REPORT.md']
 assert m['version']==1 and m['excluded_anchor_files']==sorted(SPECIAL)
 if scan(root)!=m['entries']:raise ValueError('exact payload tree/metadata/hash mismatch')
 treefile=project/'sources/preprints-tree.json'
 assert digest(treefile)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=json.loads(treefile.read_text());assert len(tree['tree'])==13223 and tree['truncated'] is False
 blobs={x['path']:x for x in tree['tree'] if x['type']=='blob'}
 src=json.loads((root/'packet/private/source-authentication.json').read_text())
 for r in src:
  e=blobs.get(r['path'],blobs.get(r['path'].removeprefix('preprints/')));assert e
  data=(root/r['local']).read_bytes()
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==r['git_blob_sha1']
  assert len(data)==e['size']==r['size'] and hashlib.sha256(data).hexdigest()==r['sha256']
 prim=json.loads((root/'packet/private/primary-authentication.json').read_text())
 for r in prim:
  p=root/r['local'];assert digest(p)==r['sha256'] and digest(p.with_suffix('.txt'))==r['text_sha256']
 # External binding checks do not silently replace an initial binding with a later file.
 initial=json.loads((root/'work/start-inputs.json').read_text())
 for rel,expected in initial.items():
  p=project/rel
  if expected['type']=='file':
   d=desc(p)
   if d!=expected:raise ValueError('stable external input changed: '+rel)
  else:
   if not p.is_dir() or p.is_symlink() or stat.S_IMODE(p.stat().st_mode)!=expected['mode']:raise ValueError('external directory changed: '+rel)
 more=json.loads((root/'work/additional-inputs-start.json').read_text())
 for rel,e in more.items():
  if e.get('stability')=='mutable_navigation_only':continue
  if digest(project/rel)!=e['sha256'] or (project/rel).stat().st_size!=e['size']:raise ValueError('additional stable input changed: '+rel)
 copies=json.loads((root/'packet/private/input-copies.json').read_text())
 for r in copies:assert digest(root/r['copy'])==r['sha256']==digest(project/r['original'])
 return {'status':'REVIEW_ARTIFACTS_VERIFIED','payload_files':sum(d['type']=='file' for d in m['entries'].values()),'source_bodies':len(src),'primary_pdf_text_pairs':len(prim),'stable_external_files':sum(d['type']=='file' for d in initial.values())+len(more),'mathematical_gate':False}

def main():
 a=argparse.ArgumentParser(description=__doc__)
 for name in ['root','project','finalhash','manifesthash','reporthash']:a.add_argument('--'+name,required=True)
 args=a.parse_args()
 try:
  out=verify(Path(args.root),Path(args.project),{'FINAL.json':args.finalhash,'packet/MANIFEST.json':args.manifesthash,'REPORT.md':args.reporthash})
 except (OSError,ValueError,KeyError,AssertionError) as e:
  print('REJECT: '+(str(e) or type(e).__name__));return 1
 print(json.dumps(out,sort_keys=True));return 0
if __name__=='__main__':sys.exit(main())
