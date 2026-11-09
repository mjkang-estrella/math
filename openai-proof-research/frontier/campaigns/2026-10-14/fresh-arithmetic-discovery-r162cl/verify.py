#!/usr/bin/env python3
"""Read-only explicit-anchor verifier; artifact authentication, not mathematics."""
import argparse,hashlib,json,stat
from pathlib import Path,PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
ROOT_SHA='814eaba6f65802514be8a76c437dca25e9f8f7b4'
EXCLUDED={'MANIFEST.json','REPORT.md'}
def digest(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 records=[]
 def visit(p):
  rel=p.relative_to(root).as_posix();mode=p.lstat().st_mode
  assert not stat.S_ISLNK(mode),('symlink',rel)
  if stat.S_ISDIR(mode):
   records.append({'path':rel,'kind':'directory','full_mode':mode})
   for q in sorted(p.iterdir(),key=lambda q:q.name):visit(q)
  else:
   assert stat.S_ISREG(mode),('special file',rel)
   if rel in EXCLUDED:return
   b=p.read_bytes();records.append({'path':rel,'kind':'file','full_mode':mode,'bytes':len(b),'sha256':digest(b)})
 visit(root)
 return sorted(records,key=lambda x:x['path'])
def verify_packet(root,anchors,planned=None):
 assert len(anchors)==3 and all(len(x)==64 and all(c in '0123456789abcdef' for c in x) for x in anchors)
 final=root.joinpath('FINAL.md').read_bytes()
 manifest,report=(planned if planned is not None else (root.joinpath('MANIFEST.json').read_bytes(),root.joinpath('REPORT.md').read_bytes()))
 assert tuple(map(digest,(final,manifest,report)))==tuple(anchors),'detached anchor mismatch'
 m=json.loads(manifest);assert m['version']==1
 paths=[x['path'] for x in m['records']]
 assert paths==sorted(paths) and len(paths)==len(set(paths)),'unsorted/duplicate records'
 for p in paths:
  q=PurePosixPath(p)
  assert p=='.' or (not q.is_absolute() and '..' not in q.parts and q.as_posix()==p and '\\' not in p),'unsafe path'
 assert m['records']==inventory(root),'membership/hash/length/full-mode mismatch'
 assert 'FINAL.md' in paths
 if planned is None:
  assert {p:root.joinpath(p).lstat().st_mode for p in EXCLUDED}==m['envelope_modes'],'envelope full modes'
 assert anchors[0].encode() in report and anchors[1].encode() in report,'report anchors absent'
 return m

def verify_bindings(root):
 private=root/'private'
 entries=json.loads((private/'source-tree.json').read_text());assert len(entries)==15
 assert next(x for x in entries if x['path'].count('/')==1)['sha']==ROOT_SHA
 bindings=json.loads((private/'source-bindings.json').read_text());assert len(bindings)==11
 bypath={x['path']:x for x in entries}
 for b in bindings:
  p=root/b['path'];raw=p.read_bytes();e=bypath[b['upstream']]
  assert b['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']
  assert len(raw)==b['bytes']==e['size'] and digest(raw)==b['sha256']
  assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==b['git_blob']==e['sha']
  assert stat.S_ISREG(p.lstat().st_mode) and stat.S_IMODE(p.lstat().st_mode)==int(e['mode'],8)&0o777
 for e in entries:
  if e['type']!='tree':continue
  prefix=e['path']+'/'
  children=[x for x in entries if x['path'].startswith(prefix) and '/' not in x['path'][len(prefix):]]
  data=b''
  for x in sorted(children,key=lambda x:x['path'].rsplit('/',1)[1]+('/' if x['type']=='tree' else '')):
   data+=x['mode'].lstrip('0').encode()+b' '+x['path'].rsplit('/',1)[1].encode()+b'\0'+bytes.fromhex(x['sha'])
  assert hashlib.sha1(b'tree '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']
 for b in json.loads((private/'primary-bindings.json').read_text()):
  if 'error' in b:continue
  raw=(private/'primary'/(b['name']+'.pdf')).read_bytes()
  assert len(raw)==b['bytes'] and digest(raw)==b['sha256']
 comp=private/'companion';ct=json.loads((comp/'tree-selection.json').read_text());ce={x['path']:x for x in ct['entries']}
 for b in json.loads((comp/'bindings.json').read_text()):
  raw=(comp/b['path']).read_bytes();e=ce[b['path']]
  assert len(raw)==b['bytes']==e['size'] and digest(raw)==b['sha256']
  assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==b['git_blob']==e['sha']
  assert b['url']=='https://raw.githubusercontent.com/'+ct['repository']+'/'+ct['commit']+'/'+b['path']
 project=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
 allowed=['frontier/campaigns/2026-10-14/discovery-arithmetic-r162ck-parent/assessment.md']+['frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ck/'+x for x in ['private/DERIVATION.md','private/WORKING.md','private/READING-LIMITS.md','FINAL.md']]
 eb=json.loads((private/'exception-bindings.json').read_text());assert [b['original'] for b in eb]==allowed
 for b in eb:
  original=project/b['original'];copy=root/b['copy'];raw=original.read_bytes()
  assert raw==copy.read_bytes() and len(raw)==b['bytes'] and digest(raw)==b['sha256']
  assert original.lstat().st_mode==copy.lstat().st_mode==b['full_mode']

def main():
 p=argparse.ArgumentParser();p.add_argument('root');p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
 root=Path(a.root).resolve();m=verify_packet(root,(a.final_sha256,a.manifest_sha256,a.report_sha256));verify_bindings(root)
 files=sum(x['kind']=='file' for x in m['records']);dirs=len(m['records'])-files
 print(json.dumps({'artifact':'MATCH','payload_files':files,'whole_root_files':files+2,'directories_including_root':dirs,'payload_bytes':sum(x.get('bytes',0) for x in m['records']),'mathematical_gate':False}))
if __name__=='__main__':main()
