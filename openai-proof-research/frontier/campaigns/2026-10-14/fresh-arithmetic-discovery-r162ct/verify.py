#!/usr/bin/env python3
"""Read-only packet verifier. Supply all THREE independent detached SHA256 anchors.
Artifact integrity only; not a mathematical gate. No discovery outside exact inputs.
"""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
EXACT_ORIGINALS=[
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162cs-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cs/private/COMPARISON.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cs/WORKLOG.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cs/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cs/FINAL.md']
ROOT_REL='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct'

def require(ok,msg):
 if not ok: raise ValueError(msg)
def digest(data): return hashlib.sha256(data).hexdigest()
def safe(s):
 p=PurePosixPath(s)
 require(isinstance(s,str) and s and not p.is_absolute() and '\\' not in s and all(x not in ('','.','..') for x in s.split('/')), 'unsafe member')
 return s

def inventory(root,excluded=()):
 files=[]; dirs=[]
 def visit(p,rel):
  st=p.lstat(); require(stat.S_ISDIR(st.st_mode),'directory required: '+rel)
  dirs.append({'path':rel,'mode':oct(st.st_mode)})
  for child in sorted(p.iterdir(),key=lambda x:x.name):
   rr=child.name if rel=='.' else rel+'/'+child.name
   safe(rr); st=child.lstat()
   require(not stat.S_ISLNK(st.st_mode),'symlink: '+rr)
   if stat.S_ISDIR(st.st_mode): visit(child,rr)
   else:
    require(stat.S_ISREG(st.st_mode),'not regular: '+rr)
    if rr not in excluded:
     data=child.read_bytes(); files.append({'path':rr,'bytes':len(data),'sha256':digest(data),'mode':oct(st.st_mode)})
 visit(root,'.')
 return sorted(files,key=lambda x:x['path']),sorted(dirs,key=lambda x:x['path'])

def check_payload(root,m,excluded=()):
 require(set(m)=={'schema','pin','files','directories'},'manifest keys')
 require(m['schema']==1 and m['pin']==PIN,'schema/pin')
 for kind in ['files','directories']:
  records=m[kind]; names=[x['path'] for x in records]
  require(names==sorted(names) and len(names)==len(set(names)),'unsorted/duplicate '+kind)
  for x in records:
   if x['path']!='.': safe(x['path'])
   else: require(kind=='directories','root is not file')
 files,dirs=inventory(root,excluded)
 require(files==m['files'],'file membership/hash/length/full-mode mismatch')
 require(dirs==m['directories'],'directory membership/full-mode mismatch')
 return len(files),len(dirs),sum(x['bytes'] for x in files)

def anchor(path,want):
 require(len(want)==64 and all(c in '0123456789abcdef' for c in want),'invalid anchor')
 st=path.lstat(); require(st.st_mode==0o100644,'anchor file full mode')
 data=path.read_bytes(); require(digest(data)==want,'detached anchor mismatch: '+path.name)
 return data

def check_bindings(root,project):
 entries=json.loads((root/'private/source-tree.json').read_text())
 bindings=json.loads((root/'private/source-bindings.json').read_text())
 require(len(entries)==15 and len(bindings)==11,'source counts')
 complete=(project/'sources/preprints-tree.json').read_bytes()
 require(digest(complete)==TREE_SHA,'complete tree anchor')
 ct=json.loads(complete)
 all_entries=ct['tree'] if isinstance(ct,dict) else ct
 prefix='preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026'
 require([x for x in all_entries if x['path']==prefix or x['path'].startswith(prefix+'/')]==entries,'complete source selection')
 by={e['path']:e for e in entries}; require(len(by)==15,'duplicate source entry')
 require({b['path'] for b in bindings}=={e['path'] for e in entries if e['type']=='blob'},'source blob membership')
 for b in bindings:
  safe(b['local']); p=root/b['local']; st=p.lstat(); data=p.read_bytes(); e=by[b['path']]
  require(st.st_mode==int(b['mode'],8) and stat.S_ISREG(st.st_mode),'source full mode')
  require(len(data)==b['bytes']==e['size'] and digest(data)==b['sha256'],'source bytes')
  gh=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  require(gh==b['git']==e['sha'],'source Git blob')
  require(b['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+b['path'],'pinned URL')
 for e in entries:
  if e['type']!='tree': continue
  children=[x for x in entries if str(PurePosixPath(x['path']).parent)==e['path']]
  children.sort(key=lambda x:PurePosixPath(x['path']).name+('/' if x['type']=='tree' else ''))
  data=b''.join((x['mode'].lstrip('0')+' '+PurePosixPath(x['path']).name).encode()+b'\0'+bytes.fromhex(x['sha']) for x in children)
  require(hashlib.sha1(b'tree '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha'],'source Git tree')
 ex=json.loads((root/'private/exceptions.json').read_text())
 require([x['original'] for x in ex]==EXACT_ORIGINALS,'exact exception list')
 for e in ex:
  safe(e['copy'])
  for p in [project/e['original'],root/e['copy']]:
   st=p.lstat(); require(stat.S_ISREG(st.st_mode) and st.st_mode==int(e['mode'],8),'exception full mode')
   data=p.read_bytes(); require(len(data)==e['bytes'] and digest(data)==e['sha256'],'exception unchanged/copy')
 for e in json.loads((root/'private/primary/access.json').read_text()):
  data=(root/'private/primary'/ (e['name']+'.pdf')).read_bytes()
  require(len(data)==e['bytes'] and digest(data)==e['sha256'],'primary binding')

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for x in ['root','final','manifest','report']: ap.add_argument('--'+x,required=True)
 a=ap.parse_args(); root=Path(a.root).absolute()
 project=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
 require(root==project/ROOT_REL,'exact own root required')
 anchor(root/'FINAL.md',a.final)
 m=json.loads(anchor(root/'MANIFEST.json',a.manifest))
 report=anchor(root/'REPORT.md',a.report).decode()
 require(a.final in report and a.manifest in report,'REPORT detached bindings')
 counts=check_payload(root,m,{'MANIFEST.json','REPORT.md'})
 check_bindings(root,project)
 print(json.dumps({'artifact':'MATCH','payload_files':counts[0],'directories_including_root':counts[1],'payload_bytes':counts[2],'whole_root_files':counts[0]+2,'mathematical_gate':False}))
if __name__=='__main__': main()
