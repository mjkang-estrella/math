#!/usr/bin/env python3
"""Read-only byte/inventory verifier. No mathematical or contribution gate. MIT."""
import argparse,hashlib,json,os,re,stat,sys
from pathlib import Path,PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def need(condition,message):
 if not condition:raise ValueError(message)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def regular(path):need(not path.is_symlink() and stat.S_ISREG(path.stat().st_mode),'not a regular file: '+str(path))
def safe(s):
 need(isinstance(s,str) and s and '\\' not in s,'bad path')
 p=PurePosixPath(s);need(not p.is_absolute() and '..' not in p.parts and str(p)==s,'unsafe/noncanonical path')
 return s
def inventory(root):
 files={};dirs=['.']
 def visit(p):
  for e in sorted(os.scandir(p),key=lambda e:e.name):
   q=Path(e.path);rel=q.relative_to(root).as_posix();need(not e.is_symlink(),'symlink: '+rel)
   if e.is_dir(follow_symlinks=False):dirs.append(rel);visit(q)
   else:
    need(e.is_file(follow_symlinks=False),'special file: '+rel)
    files[rel]={'bytes':q.stat().st_size,'sha256':digest(q)}
 visit(root)
 return files,sorted(dirs)
def verify(root,finalhash,reporthash):
 need(re.fullmatch('[0-9a-f]{64}',finalhash) is not None,'invalid detached FINAL hash')
 need(re.fullmatch('[0-9a-f]{64}',reporthash) is not None,'invalid detached report hash')
 need(root.is_dir() and not root.is_symlink(),'invalid root')
 need((root/'packet').is_dir() and not (root/'packet').is_symlink(),'invalid packet root')
 for n in ['FINAL.json','REPORT.md','packet/MANIFEST.json']:regular(root/n)
 need(digest(root/'FINAL.json')==finalhash,'detached FINAL mismatch')
 need(digest(root/'REPORT.md')==reporthash,'detached report mismatch')
 final=json.loads((root/'FINAL.json').read_text())
 need(final['pin']==PIN and final['status']=='PREFREEZE' and final['frozen'] is False and final['nominee'] is None,'scope/status mismatch')
 need(final['report_sha256']==reporthash,'report binding mismatch')
 need(digest(root/'packet/MANIFEST.json')==final['manifest_sha256'],'manifest binding mismatch')
 manifest=json.loads((root/'packet/MANIFEST.json').read_text())
 need(manifest['schema']==1 and manifest['pin']==PIN,'manifest schema/pin mismatch')
 expected={}
 for rec in manifest['files']:
  s=safe(rec['path']);need(s not in expected and s!='MANIFEST.json','duplicate/self file entry');expected[s]={'bytes':rec['bytes'],'sha256':rec['sha256']}
 ed=manifest['directories'];need(ed==sorted(set(ed)) and '.' in ed,'directory list mismatch')
 for s in ed:safe(s)
 files,dirs=inventory(root/'packet');files.pop('MANIFEST.json',None)
 need(files==expected,'exact payload inventory/hash mismatch');need(dirs==ed,'exact directory inventory mismatch')
 need(digest(root/'packet/public/report.md')==final['public_report_sha256'],'public report binding mismatch')
 treepath=root/'packet/private/context/preprints-tree.json'
 need(digest(treepath)==final['tree_sha256'],'tree binding mismatch')
 tree=json.loads(treepath.read_text());need(tree['truncated'] is False and len(tree['tree'])==13223,'incomplete canonical tree')
 bypath={e['path']:e for e in tree['tree']};need(len(bypath)==13223,'duplicate tree path')
 upstream=json.loads((root/'packet/private/context/upstream.json').read_text());need(upstream['commit']==PIN,'upstream pin mismatch')
 records=json.loads((root/'packet/private/upstream/canonical-register.json').read_text());seen=set();retained=0
 for rec in records:
  c=rec['canonical'];s=c['path'];need(s not in seen,'duplicate source record');seen.add(s)
  need(bypath.get(s)==c and c['type']=='blob','canonical full metadata mismatch')
  need(rec['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+s,'raw URL mismatch')
  local=safe(rec['local']);need(local=='packet/private/upstream/'+s,'local canonical path mismatch');p=root/local
  if rec['retained']:
   regular(p);b=p.read_bytes();need(len(b)==rec['bytes']==c['size'],'source size mismatch')
   need(hashlib.sha256(b).hexdigest()==rec['sha256'],'source SHA mismatch')
   need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==c['sha'],'Git blob mismatch');retained+=1
  else:need(not p.exists() and not p.is_symlink(),'removed body reappeared')
 need(len(records)==final['canonical_acquired'] and retained==final['canonical_retained'],'source counts mismatch')
 prim=json.loads((root/'packet/private/primary/register.json').read_text())
 for rec in prim:
  need(rec['extraction_exit']==0,'unrecorded extraction failure')
  need(digest(root/'packet/private/primary'/(rec['name']+'.pdf'))==rec['sha256'],'primary PDF mismatch')
  need(digest(root/'packet/private/primary'/(rec['name']+'.txt'))==rec['text_sha256'],'primary text mismatch')
 for name in ['history/register.json','context/findings-register.json']:
  for rec in json.loads((root/'packet/private'/name).read_text()):
   p=root/safe(rec['local']);need(digest(p)==rec['sha256'] and p.stat().st_size==rec['bytes'],'copied evidence mismatch')
 return {'status':'INTEGRITY_ONLY_OK','payloads':len(files),'directories':len(dirs),'canonical_acquired':len(records),'canonical_retained':retained,'primary_pairs':len(prim),'final_sha256':finalhash,'report_sha256':reporthash}
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',required=True,type=Path);p.add_argument('--final-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
 try:print(json.dumps(verify(a.root,a.final_sha256,a.report_sha256),sort_keys=True))
 except Exception as e:print('REJECT: '+str(e),file=sys.stderr);return 1
 return 0
if __name__=='__main__':sys.exit(main())
