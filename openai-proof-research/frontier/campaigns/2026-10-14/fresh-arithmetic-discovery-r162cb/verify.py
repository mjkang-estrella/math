#!/usr/bin/env python3
"""Read-only artifact verifier. All three detached SHA256 anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
STATEMENT_SHA = 'b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a'
ROOT = 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cb'
PROJECT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
FOLDERS = (
 'preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026',
 'preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026',
)
ORIGINALS = (
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162ca-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ca/private/DERIVATION.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ca/WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ca/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ca/FINAL.md',
)
DIRECT = {'AGENTS.md': None, 'sources/upstream.json': None,
 'frontier/NEW-TEN-2026-10-14.md': [4801,6347],
 'sources/CONTENTS.md': [263076,264581]}

def sha(b):
 return hashlib.sha256(b).hexdigest()

def safe(s, root_ok=False):
 assert isinstance(s,str) and s and '\\' not in s
 if root_ok and s=='.': return
 p=PurePosixPath(s)
 assert not p.is_absolute() and str(p)==s and all(x not in ('.','..') for x in p.parts)

def pathsafe(base, rel):
 safe(rel)
 p=base
 for part in PurePosixPath(rel).parts:
  p=p/part
  assert not p.is_symlink(), f'symlink: {rel}'
 return p

def inventory(root):
 assert root.is_dir() and not root.is_symlink()
 files=[]; dirs=[{'path':'.','mode':root.lstat().st_mode}]
 for current, dn, fn in os.walk(root, followlinks=False):
  for name in dn:
   p=Path(current)/name; assert stat.S_ISDIR(p.lstat().st_mode), str(p)
   dirs.append({'path':p.relative_to(root).as_posix(),'mode':p.lstat().st_mode})
  for name in fn:
   p=Path(current)/name; assert stat.S_ISREG(p.lstat().st_mode), str(p)
   b=p.read_bytes()
   files.append({'path':p.relative_to(root).as_posix(),'bytes':len(b),'sha256':sha(b),'mode':p.lstat().st_mode})
 return sorted(files,key=lambda x:x['path']), sorted(dirs,key=lambda x:x['path'])

def check_inventory(root, records, directories, extras=()):
 for seq,rd in [(records,False),(directories,True)]:
  names=[x['path'] for x in seq]
  assert names==sorted(names) and len(names)==len(set(names)), 'unsorted/duplicate records'
  for x in seq: safe(x['path'],rd)
 files,dirs=inventory(root)
 assert dirs==directories, 'directory membership/full modes'
 actual={x['path']:x for x in files}; expected={x['path']:x for x in records}
 assert set(actual)==set(expected)|set(extras), 'file membership'
 for name,item in expected.items(): assert actual[name]==item, f'file binding: {name}'
 for name in extras: assert actual[name]['mode']==0o100644, f'extra full mode: {name}'
 return len(files),len(dirs)

def verify(root, final_anchor, manifest_anchor, report_anchor):
 assert Path.cwd()==PROJECT, 'run from the authorized project workdir'
 assert root.resolve()==PROJECT/ROOT and not root.is_symlink()
 for name,anchor in [('FINAL.md',final_anchor),('MANIFEST.json',manifest_anchor),('REPORT.md',report_anchor)]:
  assert len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor)
  assert sha(pathsafe(root,name).read_bytes())==anchor, f'detached anchor: {name}'
 m=json.loads((root/'MANIFEST.json').read_text())
 assert m['schema']=='r162cb-artifact-v1' and m['pin']==PIN
 counts=check_inventory(root,m['files'],m['directories'],('MANIFEST.json','REPORT.md'))
 assert sha((root/'STATEMENT.md').read_bytes())==STATEMENT_SHA
 assert json.loads((root/'private/FREEZE.json').read_text())['sha256']==STATEMENT_SHA
 treebytes=pathsafe(PROJECT,'sources/preprints-tree.json').read_bytes()
 assert len(treebytes)==4858136 and sha(treebytes)==TREE_SHA
 tree=json.loads(treebytes); assert tree['truncated'] is False and len(tree['tree'])==13223
 selected=[e for e in tree['tree'] if any(e['path']==f or e['path'].startswith(f+'/') for f in FOLDERS)]
 bindings=json.loads((root/'private/source-bindings.json').read_text())
 assert bindings==selected and len(bindings)==26
 receipts=json.loads((root/'private/source-receipt.json').read_text())
 assert len(receipts)==20 and len({x[0] for x in receipts})==20
 receipt_map={x[0]:x for x in receipts}
 for e in bindings:
  if e['type']=='blob':
   b=pathsafe(root,'private/source/'+e['path']).read_bytes()
   assert len(b)==e['size'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
   assert receipt_map[e['path']]==[e['path'],len(b),sha(b)] and e['mode']=='100644'
  else:
   assert e['type']=='tree' and e['mode']=='040000'
   children=[c for c in bindings if str(PurePosixPath(c['path']).parent)==e['path']]
   children.sort(key=lambda c:(PurePosixPath(c['path']).name+('/' if c['type']=='tree' else '')).encode())
   b=b''.join(c['mode'].lstrip('0').encode()+b' '+PurePosixPath(c['path']).name.encode()+b'\0'+bytes.fromhex(c['sha']) for c in children)
   assert hashlib.sha1(b'tree '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha'], e['path']
 completed=json.loads((root/'private/completed-bindings.json').read_text())
 assert [x['original'] for x in completed]==list(ORIGINALS)
 for x in completed:
  p=pathsafe(PROJECT,x['original']); b=p.read_bytes(); c=pathsafe(root,x['copy'])
  assert len(b)==x['bytes'] and sha(b)==x['sha256'] and p.lstat().st_mode==x['mode']
  assert c.read_bytes()==b and c.lstat().st_mode==x['mode']
 direct=json.loads((root/'private/direct-bindings.json').read_text())
 assert len(direct)==4 and {x['original'] for x in direct}==set(DIRECT)
 for x in direct:
  assert x['span']==DIRECT[x['original']]
  p=pathsafe(PROJECT,x['original'])
  with p.open('rb') as f:
   if x['span'] is None: b=f.read()
   else:
    lo,hi=x['span']; f.seek(lo); b=f.read(hi-lo)
  assert len(b)==x['bytes'] and sha(b)==x['sha256'] and p.lstat().st_mode==x['mode']
  assert pathsafe(root,x['copy']).read_bytes()==b
 assert json.loads((root/'private/direct/upstream.json').read_text())['commit']==PIN
 acquisitions=json.loads((root/'private/primary/acquisition.json').read_text())
 assert {x['name'] for x in acquisitions}=={'HS','FHMW','ABPS','SW','BPS','DKMS'} and len(acquisitions)==6
 for x in acquisitions:
  b=(root/'private/primary'/f"{x['name']}.pdf").read_bytes()
  assert len(b)==x['bytes'] and sha(b)==x['sha256']
  assert (root/'private/primary'/f"{x['name']}.txt").stat().st_size==x['text_bytes']
 report=(root/'REPORT.md').read_text()
 assert final_anchor in report and manifest_anchor in report
 return {'artifact':'MATCH','payload_records':len(m['files']),'whole_root_files':counts[0],'directories_including_root':counts[1], 'source_blobs':20,'source_trees':6,'completed_original_copy_pairs':5,'mathematical_gate':None}

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--root',required=True,type=Path)
 p.add_argument('--final-sha256',required=True)
 p.add_argument('--manifest-sha256',required=True)
 p.add_argument('--report-sha256',required=True)
 a=p.parse_args()
 print(json.dumps(verify(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256),sort_keys=True))
