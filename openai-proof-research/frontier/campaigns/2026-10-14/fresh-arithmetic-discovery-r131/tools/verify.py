"""Offline, read-only artifact verifier. Hashes must come from detached handoff.
Usage: python -B tools/verify.py ROOT FINAL_SHA MANIFEST_SHA REPORT_SHA [--project PROJECT]
No network, subprocess, mutation, repair, imports of packet code, or mathematical grading.
"""
import argparse,hashlib,json,os,stat
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('final_sha');p.add_argument('manifest_sha');p.add_argument('report_sha');p.add_argument('--project',type=Path);a=p.parse_args()
r=a.root
ENV=['envelopes/FINAL.md','envelopes/MANIFEST.json','envelopes/REPORT.md']
def sha(b):return hashlib.sha256(b).hexdigest()
def require(x,msg):
 if not x:raise SystemExit('REJECT: '+msg)
def raw(path):
 s=path.lstat();require(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'not a single-link regular file: '+str(path));return path.read_bytes()
require(r.is_dir() and not r.is_symlink(),'root is not a real directory')
for rel,h in zip(ENV,[a.final_sha,a.manifest_sha,a.report_sha]):
 require(len(h)==64 and all(c in '0123456789abcdef' for c in h),'invalid detached anchor')
 require(sha(raw(r/rel))==h,'detached envelope mismatch: '+rel)
manifest=json.loads(raw(r/ENV[1]));require(manifest['schema']==1,'unknown schema')
files={};dirs=[]
for base,ds,fs in os.walk(r,topdown=True,followlinks=False):
 for d in ds:
  q=Path(base)/d;require(not q.is_symlink(),'symlink directory');dirs.append(q.relative_to(r).as_posix())
 for f in fs:
  q=Path(base)/f;rel=q.relative_to(r).as_posix();b=raw(q)
  if rel not in ENV:files[rel]={'size':len(b),'sha256':sha(b)}
require(sorted(dirs)==manifest['directories'],'directory membership mismatch')
require(set(files)==set(manifest['files']),'file membership mismatch')
for rel,rec in files.items():require(rec==manifest['files'][rel],'payload mismatch: '+rel)
source=r/'private/source/authentication.json'
if source.exists():
 records=json.loads(raw(source))
 for o in records:
  b=raw(r/o['local']);require(len(b)==o['size'] and sha(b)==o['sha256'],'source hash: '+o['local'])
  require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==o['sha'],'source Git blob: '+o['local'])
 if a.project:
  tree=raw(a.project/'sources/preprints-tree.json');require(sha(tree)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','complete tree changed')
  import re
  chosen={}
  for match in re.finditer(rb'\{[^{}]*"path"\s*:\s*"[^"\r\n]+"[^{}]*\}',tree):
   if b'The-Blockwise-Alperin-Weight-Conjecture-September-23-2026/' in match.group():
    o=json.loads(match.group());chosen[o['path']]=o
  for o in records:
   require(o['path'] in chosen,'canonical path missing');require(all(chosen[o['path']][k]==o[k] for k in ['sha','size','type']),'canonical metadata mismatch')
if a.project:
 ids=json.loads(raw(r/'private/history/incoming-originals.json'))
 for o in ids:
  b=raw(a.project/o['path']);require(len(b)==o['bytes'] and sha(b)==o['sha256'],'incoming original changed: '+o['path'])
  if 'selected_copy' in o:
   if o['selection']=='whole original':selected=b
   else:
    lines=b.splitlines(keepends=True);selected=b'\n'.join(b''.join(lines[lo-1:hi]) for lo,hi in o['ranges_inclusive'])
   require(raw(r/o['selected_copy'])==selected,'selected membership mismatch: '+o['selected_copy'])
 # The acceptance check selects bytes before comparing, never decodes the journal.
 meta=json.loads(raw(r/'private/history/acceptance-selection.json'));selected=[]
 with (a.project/meta['original']).open('rb') as f:
  for i,line in enumerate(f,1):
   if i>=meta['stop_before_line']:break
   if i>=meta['start_line']:selected.append(line)
 b=b''.join(selected);require(sha(b)==meta['selected_sha256'] and b==raw(r/'private/history/acceptance-section.txt'),'acceptance selection changed')
print('VERIFIED artifact bytes/membership:',len(files),'payload files,',len(dirs),'directories; detached envelopes matched.'+(' Named original identities and canonical source membership matched.' if a.project else ''))
