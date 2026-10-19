from pathlib import Path
import hashlib,json,os,shutil,stat,subprocess,tempfile
R=Path(__file__).resolve().parents[1];P=R/'packet';REPO=R.parents[3];TREE=REPO/'sources/preprints-tree.json';VERIFY=P/'public/verify.py'
def sh(b):return hashlib.sha256(b).hexdigest()
def snap(root):
 d={}
 for p in sorted(root.rglob('*')):
  if p==R/'controls.json':continue
  s=p.lstat();k=p.relative_to(root).as_posix()
  d[k]=dict(type='file' if stat.S_ISREG(s.st_mode) else 'dir' if stat.S_ISDIR(s.st_mode) else 'other',mode=stat.S_IMODE(s.st_mode),nlink=s.st_nlink)
  if stat.S_ISREG(s.st_mode):d[k].update(bytes=s.st_size,sha256=sh(p.read_bytes()))
 return d
def reanchor(p,f):
 m=json.loads((p/'MANIFEST.json').read_text())
 for k,v in m['files'].items():
  q=p/k;s=q.lstat();b=q.read_bytes();v.update(sha256=sh(b),bytes=len(b),mode=stat.S_IMODE(s.st_mode),nlink=s.st_nlink)
 b=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode();(p/'MANIFEST.json').write_bytes(b);f.write_text(sh(b)+'\n')
before=snap(R);tree_before=(sh(TREE.read_bytes()),stat.S_IMODE(TREE.stat().st_mode),TREE.stat().st_nlink)
results=[]
names=['baseline','missing-final-argument','wrong-final','public-byte-change','missing-file','extra-file','extra-directory','symlink','hardlink','mode','manifest-change','reanchored-raw-url','reanchored-full-record','reanchored-primary-receipt','detached-inside-packet','deny-payload-read','deny-tree-read']
for name in names:
 with tempfile.TemporaryDirectory(prefix='control-',dir=R/'scratch') as td:
  b=Path(td);p=b/'packet';shutil.copytree(P,p);f=b/'FINAL.sha256';shutil.copy2(R/'FINAL.sha256',f)
  target=p/'public/report.md';cmd=['python',str(VERIFY),'--packet',str(p),'--finalhash',str(f),'--tree',str(TREE)]
  if name=='missing-final-argument':cmd=cmd[:4]+cmd[6:]
  elif name=='wrong-final':f.write_text('0'*64+'\n')
  elif name=='public-byte-change':target.write_bytes(target.read_bytes()+b'\nMUTATION\n')
  elif name=='missing-file':target.unlink()
  elif name=='extra-file':(p/'extra').write_text('extra')
  elif name=='extra-directory':(p/'extra-empty').mkdir()
  elif name=='symlink':target.unlink();target.symlink_to(p/'public/other-screens.md')
  elif name=='hardlink':target.unlink();os.link(p/'public/other-screens.md',target)
  elif name=='mode':target.chmod(0o600)
  elif name=='manifest-change':(p/'MANIFEST.json').write_bytes((p/'MANIFEST.json').read_bytes()+b' ')
  elif name=='reanchored-raw-url':
   q=p/'private/canonical.json';a=json.loads(q.read_text());a[0]['url']=a[0]['url'].replace('/'+a[0]['url'].split('/')[5]+'/', '/wrong/') if False else a[0]['url']+'?wrong';q.write_text(json.dumps(a));reanchor(p,f)
  elif name=='reanchored-full-record':
   q=p/'private/canonical.json';a=json.loads(q.read_text());a[0]['canonical']['url']+='?wrong';q.write_text(json.dumps(a));reanchor(p,f)
  elif name=='reanchored-primary-receipt':
   q=p/'private/primary/acquisition.json';a=json.loads(q.read_text());a[0]['text_sha256']='0'*64;q.write_text(json.dumps(a));reanchor(p,f)
  elif name=='detached-inside-packet':
   f=p/'fake-FINAL';f.write_text((R/'FINAL.sha256').read_text());cmd[5]=str(f)
  elif name in ['deny-payload-read','deny-tree-read']:
   denied=str(target if name=='deny-payload-read' else TREE)
   runner=b/'deny.py';runner.write_text('import sys,runpy,os\n'+'denied='+repr(denied)+'\n'+'def audit(event,args):\n if event=="open" and isinstance(args[0],(str,bytes)) and os.fsdecode(args[0])==denied: raise PermissionError("deliberate read denial")\nsys.addaudithook(audit)\nsys.argv='+repr(cmd[1:])+'\nrunpy.run_path('+repr(str(VERIFY))+',run_name="__main__")\n')
   cmd=['python',str(runner)]
  c0=snap(p);z=subprocess.run(cmd,capture_output=True,text=True);c1=snap(p)
  expected=0 if name=='baseline' else 1
  ok=(z.returncode==0) if expected==0 else (z.returncode!=0)
  results.append(dict(case=name,expected='accept' if expected==0 else 'reject',exit=z.returncode,as_expected=ok,stdout=z.stdout,stderr=z.stderr,copy_unchanged_by_verifier=c0==c1,copy_before_sha256=sh(json.dumps(c0,sort_keys=True).encode()),copy_after_sha256=sh(json.dumps(c1,sort_keys=True).encode())))
after=snap(R);tree_after=(sh(TREE.read_bytes()),stat.S_IMODE(TREE.stat().st_mode),TREE.stat().st_nlink)
assert before==after,'actual author root changed during copied tests'
assert tree_before==tree_after,'external canonical tree changed'
assert all(x['as_expected'] and x['copy_unchanged_by_verifier'] for x in results),results
out=dict(purpose='artifact integrity only; no mathematical gate',cases=results,all_expected=True,whole_preexisting_author_root_unchanged=True,sole_new_output='controls.json',original_before=before,original_after=after,external_tree_before=tree_before,external_tree_after=tree_after,manifest_sha256=sh((P/'MANIFEST.json').read_bytes()),outside_report_sha256=sh((R/'REPORT.md').read_bytes()))
(R/'controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(cases=len(results),all_expected=True,original_unchanged=True,controls_sha256=sh((R/'controls.json').read_bytes()))))
