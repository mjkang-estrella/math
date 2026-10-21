"""Small OWN-manifest selection; never certifies incoming-original archives."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,stat
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r116');F=R/'packet/private/copied-controls';F.mkdir(exist_ok=False)
def h(b):return hashlib.sha256(b).hexdigest()
selection=['packet/tools/verify.py','packet/notes/quadratic-bsd-reduction.md','packet/source-identities.json']
for rel in selection:
 p=F/rel;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/rel,p)
(F/'FINAL.md').write_text('Disposable selected-copy control only. No inherited original manifest.\n')
(F/'REPORT.md').write_text('Three selected payloads, no whole-original claim.\n')
files={p.relative_to(F).as_posix():{'size':p.stat().st_size,'sha256':h(p.read_bytes())} for p in sorted((F/'packet').rglob('*')) if p.is_file()}
dirs=sorted(p.relative_to(F).as_posix() for p in F.rglob('*') if p.is_dir())
(F/'MANIFEST.json').write_text(json.dumps({'schema':'r116-exact-payload-v1','directories':dirs,'files':files},indent=2,sort_keys=True)+'\n')
anchors={n:h((F/n).read_bytes()) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snapshot():
 out={}
 for p in sorted(F.rglob('*')):
  s=p.lstat();out[p.relative_to(F).as_posix()]=[s.st_mode,s.st_nlink,s.st_size,h(p.read_bytes()) if p.is_file() else None]
 return h(json.dumps(out,sort_keys=True).encode())
results=[]
def run(name,expect,wrong=False):
 before=snapshot();args=[sys.executable,'-B',str(F/'packet/tools/verify.py'),str(F),'--final',anchors['FINAL.md'],'--manifest','0'*64 if wrong else anchors['MANIFEST.json'],'--report',anchors['REPORT.md']];z=subprocess.run(args,capture_output=True,text=True);after=snapshot();assert (z.returncode==0)==expect and before==after,(name,z.stderr);results.append({'case':name,'expected_accept':expect,'returncode':z.returncode,'snapshot_before':before,'snapshot_after':after,'stdout':z.stdout,'stderr':z.stderr})
run('baseline',True)
p=F/selection[1];b=p.read_bytes();p.write_bytes(b+b'altered\n');run('altered payload',False);p.write_bytes(b)
p.unlink();run('missing payload',False);p.write_bytes(b)
p=F/'packet/.extra';p.write_text('extra');run('hidden extra',False);p.unlink()
p=F/'packet/empty-extra';p.mkdir();run('empty extra directory',False);p.rmdir()
run('wrong detached manifest anchor',False,True);run('restored',True)
(R/'packet/control-results.json').write_text(json.dumps({'scope':'own three-file selected copy, not originals or whole final root','selection':selection,'anchors':anchors,'results':results},indent=2)+'\n')
print('7 copied-selection controls matched expectations; every invocation read-only.')
