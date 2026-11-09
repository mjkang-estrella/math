"""Read-only exact packet verification. Explicit detached anchors are mandatory."""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
OWN='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bn'
EXCEPTIONS=[
'frontier/campaigns/2026-10-14/discovery-arithmetic-r162bm-parent/contribution-intake/assessment.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bm/STATEMENT.md',
'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bm/private/PROOF.md',
'frontier/campaigns/2026-10-14/arithmetic-r162bm-contribution-r1/private/ASSESSMENT.md',
'frontier/campaigns/2026-10-14/arithmetic-r162bm-contribution-r1/private/READING-LIMITS.md']
def sha(b):return hashlib.sha256(b).hexdigest()
def safe(s):
 p=PurePosixPath(s)
 assert s and not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and str(p)==s
 return s
def inventory(root):
 files={};dirs={'.':root.lstat().st_mode};assert stat.S_ISDIR(dirs['.'])
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(base)/name;s=p.relative_to(root).as_posix();safe(s);m=p.lstat().st_mode
   assert not stat.S_ISLNK(m),s
   if stat.S_ISDIR(m):dirs[s]=m
   else:assert stat.S_ISREG(m),s;files[s]=m
 return files,dirs
def verify(root,mh,fh,rh,project,virtual=None):
 root=Path(root);project=Path(project);virtual=virtual or {}
 assert set(virtual)<= {'MANIFEST.json','REPORT.md'}
 def read(s):return virtual[s] if s in virtual else (root/s).read_bytes()
 mb,fb,rb=read('MANIFEST.json'),read('FINAL.md'),read('REPORT.md')
 assert sha(mb)==mh,'manifest anchor';assert sha(fb)==fh,'FINAL anchor';assert sha(rb)==rh,'REPORT anchor'
 m=json.loads(mb);assert m['version']==1
 files,dirs=inventory(root)
 for s in virtual:
  assert s not in files,'virtual overwrite';files[s]=33188
 records=m['files'];names=[r['path'] for r in records]
 assert names==sorted(names) and len(names)==len(set(names)),'sorted unique files'
 for n in names:safe(n)
 assert set(files)==set(names)|{'MANIFEST.json','REPORT.md'},'exact file membership'
 dr=m['directories'];dn=[r['path'] for r in dr]
 assert dn==sorted(dn) and len(dn)==len(set(dn)),'sorted unique directories'
 assert dirs=={r['path']:r['mode'] for r in dr},'directories/full modes'
 assert files['MANIFEST.json']==m['manifest_mode'] and files['REPORT.md']==m['report_mode'],'envelope modes'
 for r in records:
  b=read(r['path']);assert len(b)==r['bytes'] and sha(b)==r['sha256'] and files[r['path']]==r['mode'],r['path']
 assert f'FINAL SHA256: {fh}' in rb.decode() and f'MANIFEST SHA256: {mh}' in rb.decode(),'report bindings'
 if m['kind']=='r162bn':
  assert root.resolve()==(project/OWN).resolve(),'authorized root'
  assert m['pin']==PIN and m['tree_sha256']==TREE
  tb=(project/'sources/preprints-tree.json').read_bytes()
  assert len(tb)==4858136 and sha(tb)==TREE
  td=json.loads(tb);entries=td['tree'] if isinstance(td,dict) else td;assert len(entries)==13223
  selected=json.loads(read('private/source-bindings.json'));assert len(selected)==39
  bypath={r['path']:r for r in entries}
  for r in selected:assert bypath[r['path']]==r
  auth=json.loads(read('private/source-authentication.json'));assert len(auth)==30
  blobs={r['path']:r for r in selected if r['type']=='blob'}
  assert {r['path'] for r in auth}==set(blobs)
  for r in auth:
   p=r['path'];safe(p);b=read('private/source/'+p);a=blobs[p]
   assert len(b)==r['size']==a['size'] and sha(b)==r['sha256']
   assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']==a['sha']
   assert files['private/source/'+p]==int(a['mode'],8)
   assert r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p
  cb=json.loads(read('private/completed-bindings.json'))
  assert [r['original'] for r in cb]==EXCEPTIONS
  for i,r in enumerate(cb,1):
   assert r['copy']==f'private/completed/{i}.md'
   p=project/r['original'];assert p.lstat().st_mode==r['mode']
   b=p.read_bytes();assert b==read(r['copy']) and len(b)==r['bytes'] and sha(b)==r['sha256']
  for a in json.loads(read('private/primary/acquisition.json')):
   b=read('private/primary/'+safe(a['name'])+'.pdf');assert len(b)==a['bytes'] and sha(b)==a['sha256']
 elif m['kind']!='tiny-control':raise AssertionError('manifest kind')
 return {'artifact_check':'MATCH','payload_files':len(names),'whole_root_files':len(files),'directories_including_root':len(dirs),'payload_bytes':sum(r['bytes'] for r in records)}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--final-sha256',required=True);p.add_argument('--report-sha256',required=True);p.add_argument('--project',default='.')
 a=p.parse_args();print(json.dumps(verify(a.root,a.manifest_sha256,a.final_sha256,a.report_sha256,a.project),sort_keys=True))
