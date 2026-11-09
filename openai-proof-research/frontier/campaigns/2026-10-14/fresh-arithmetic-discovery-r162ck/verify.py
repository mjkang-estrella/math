#!/usr/bin/env python3
"""Read-only r162ck artifact verifier. Three explicit detached anchors required."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

PROJECT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
RELROOT = 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ck'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX = 'preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026'
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
ORIGINALS = [
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162cj-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cj/private/DERIVATION.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cj/private/WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cj/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cj/FINAL.md',
]
COMPANIONS = {
 'JD-Jones-ASES/six-concyclic-lean':'5a67631e0f524ac80f199b9294b444c631fc0c3a',
 'wstrinz/mobius-ramsey':'e03b716ef2cc1cc542a06486135c01f1c4406e08',
 'wstrinz/algebraic-plus-three-ramsey':'9d345e5f66363b965f2d75d779437fda666d55ac',
 'wstrinz/radian-ramsey':'f94bedbc05dd63d08adfba83ce853ede0094fb86',
 'wstrinz/spherical-ramsey':'54b560f6b2a3436d9cd9b8978ea9b1572f1fd6c3',
}
def sha(data):
 return hashlib.sha256(data).hexdigest()
def gitsha(kind, data):
 return hashlib.sha1(kind.encode()+b' '+str(len(data)).encode()+b'\0'+data).hexdigest()
def safe(name):
 p=PurePosixPath(name)
 assert name and not p.is_absolute() and '..' not in p.parts and str(p)==name and '\\' not in name, ('unsafe',name)
 return name
def read(root,name):
 p=root/safe(name)
 assert stat.S_ISREG(p.lstat().st_mode), ('not regular',name)
 return p.read_bytes()
def anchor(root,name,expected):
 assert len(expected)==64 and all(c in '0123456789abcdef' for c in expected), ('anchor format',name)
 assert sha(read(root,name))==expected, ('anchor mismatch',name)
def inventory(root):
 assert stat.S_ISDIR(root.lstat().st_mode), 'root is not a real directory'
 files={};dirs={'.':root.lstat().st_mode}
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(base)/name; rel=p.relative_to(root).as_posix();mode=p.lstat().st_mode
   if stat.S_ISDIR(mode):dirs[rel]=mode
   else:
    assert stat.S_ISREG(mode), ('unsafe file type',rel)
    files[rel]=mode
 return files,dirs
def verify_inventory(root,final_anchor,manifest_anchor,report_anchor):
 for name,h in [('FINAL.md',final_anchor),('MANIFEST.json',manifest_anchor),('REPORT.md',report_anchor)]:anchor(root,name,h)
 manifest=json.loads(read(root,'MANIFEST.json'))
 records=manifest['files']; names=[safe(x['path']) for x in records]
 assert names==sorted(names) and len(names)==len(set(names)), 'file order/uniqueness'
 drecords=manifest['directories'];dnames=[x['path'] for x in drecords]
 assert dnames==sorted(dnames) and len(dnames)==len(set(dnames)), 'directory order/uniqueness'
 assert dnames[0]=='.'
 for name in dnames[1:]:safe(name)
 files,dirs=inventory(root)
 assert set(files)==set(names)|{'MANIFEST.json','REPORT.md'}, 'file membership'
 assert dirs=={x['path']:x['full_mode'] for x in drecords}, 'directory membership/modes'
 for x in records:
  data=read(root,x['path'])
  assert len(data)==x['bytes'] and sha(data)==x['sha256'], ('file bytes',x['path'])
  assert files[x['path']]==x['full_mode'], ('file full mode',x['path'])
 for name,mode in manifest['envelope_full_modes'].items():
  assert name in ('MANIFEST.json','REPORT.md') and files[name]==mode, ('envelope mode',name)
 assert set(manifest['envelope_full_modes'])=={'MANIFEST.json','REPORT.md'}
 return manifest

def verify_bindings(root):
 def load(name):return json.loads(read(root,name))
 tree=load('private/source-tree.json'); entries={x['path']:x for x in tree}
 assert len(tree)==len(entries)==16
 master_data=(PROJECT/'sources/preprints-tree.json').read_bytes()
 assert len(master_data)==4858136 and sha(master_data)==TREE_SHA256
 master=json.loads(master_data); master=master['tree'] if isinstance(master,dict) else master
 assert len(master)==13223
 full={x['path']:x for x in master}
 for path,e in entries.items():assert e==full[path], ('complete tree binding',path)
 blobs=load('private/source-bindings.json')
 assert len(blobs)==12 and len({x['upstream_path'] for x in blobs})==12
 assert {x['upstream_path'] for x in blobs}=={p for p,e in entries.items() if e['type']=='blob'}
 for b in blobs:
  e=entries[b['upstream_path']];data=read(root,b['path'])
  assert b['path']=='private/source/'+b['upstream_path'][len(PREFIX)+1:]
  assert b['upstream_path'].startswith(PREFIX+'/')
  assert b['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+b['upstream_path']
  assert len(data)==b['bytes']==e['size'] and sha(data)==b['sha256']
  assert gitsha('blob',data)==b['git_blob']==e['sha'] and b['upstream_mode']==e['mode']
 for path,e in entries.items():
  if e['type']!='tree':continue
  children=[v for p,v in entries.items() if str(PurePosixPath(p).parent)==path]
  children.sort(key=lambda v:(PurePosixPath(v['path']).name+('/' if v['type']=='tree' else '')).encode())
  data=b''.join((v['mode'].lstrip('0')+' '+PurePosixPath(v['path']).name).encode()+b'\0'+bytes.fromhex(v['sha']) for v in children)
  assert gitsha('tree',data)==e['sha'], ('tree object',path)
 originals=load('private/completed-bindings.json')
 assert len(originals)==5 and {x['original'] for x in originals}==set(ORIGINALS)
 for b in originals:
  original=PROJECT/b['original'];mode=original.lstat().st_mode
  assert stat.S_ISREG(mode) and mode==b['original_full_mode'] and stat.S_IMODE(mode)==b['original_mode']
  data=original.read_bytes();copy=read(root,b['copy'])
  assert data==copy and len(data)==b['bytes'] and sha(data)==b['sha256'], ('completed copy',b['original'])
 for b in load('private/primary-bindings.json'):
  data=read(root,'private/primary/'+safe(b['name'])+'.pdf')
  assert len(data)==b['bytes'] and sha(data)==b['sha256'], ('primary',b['name'])
 companions=load('private/companions/bindings.json');seen=set()
 for b in companions:
  repo=b['repository'];commit=COMPANIONS[repo];base='private/companions/'+repo.split('/')[-1]+'/'
  assert b['commit']==commit and b['url']=='https://raw.githubusercontent.com/'+repo+'/'+commit+'/'+safe(b['path'])
  key=(repo,b['path']);assert key not in seen;seen.add(key)
  meta=load(base+'tree.json');assert meta['repository']==repo and meta['commit']==commit
  e=next(x for x in meta['tree']['tree'] if x['path']==b['path'])
  data=read(root,base+b['path'])
  assert e['type']=='blob' and len(data)==b['bytes']==e['size'] and sha(data)==b['sha256']
  assert gitsha('blob',data)==b['git_blob']==e['sha']
 return {'source_blobs':12,'source_entries':16,'completed_originals':5,'companion_blobs':len(companions)}

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
 a=p.parse_args();assert Path.cwd()==PROJECT, 'required command workdir'
 root=PROJECT/RELROOT
 m=verify_inventory(root,a.final_sha256,a.manifest_sha256,a.report_sha256)
 b=verify_bindings(root)
 print(json.dumps({'artifact_check':'MATCH','payload_files':len(m['files']),'whole_root_files':len(m['files'])+2,'directories_including_root':len(m['directories']),**b},sort_keys=True))
if __name__=='__main__':main()
