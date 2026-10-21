# Creates and mutates ONLY a small copied fixture under this exclusive root.
# Not to be rerun on the sealed packet. The verifier itself is read-only.
from pathlib import Path
import hashlib,json,subprocess,sys,os,stat
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r157');F=R/'private/copied-fixture'
F.mkdir(exist_ok=False);(F/'payload').mkdir()
for src,dest in [('code/verify.py','payload/verify.py'),('notes/01-prefreeze-calculations.md','payload/math-note.md'),('code/finite_transport.py','payload/finite_transport.py')]:
 (F/dest).write_bytes((R/src).read_bytes())
E=['FINAL.md','MANIFEST.json','REPORT.md']
def digest(b):return hashlib.sha256(b).hexdigest()
def snapshot():
 files={};dirs=['.']
 for base,ds,fs in os.walk(F):
  for d in ds:dirs.append((Path(base)/d).relative_to(F).as_posix())
  for f in fs:
   p=Path(base)/f;s=p.lstat();files[p.relative_to(F).as_posix()]={'size':s.st_size,'sha256':digest(p.read_bytes()),'mode':s.st_mode,'nlink':s.st_nlink}
 return {'files':files,'dirs':sorted(dirs)}
(F/'FINAL.md').write_text('Own copied fixture only. Not a mathematical packet.\n')
(F/'REPORT.md').write_text('Independent membership; no inherited original manifest.\n')
s=snapshot();m={'schema':'r157-exact-v1','envelopes':E,'directories':s['dirs'],'files':{k:{'size':v['size'],'sha256':v['sha256']} for k,v in s['files'].items() if k not in E}}
(F/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
anchors=[digest((F/e).read_bytes()) for e in E];results=[]
def run(name,expected,hs=None):
 before=snapshot();p=subprocess.run([sys.executable,'-B',str(F/'payload/verify.py'),str(F),*(hs or anchors)],capture_output=True,text=True,timeout=10,cwd=Path.cwd());after=snapshot()
 rec={'name':name,'expected_returncode':expected,'returncode':p.returncode,'stdout':p.stdout.strip(),'verifier_unchanged':before==after};results.append(rec)
 assert p.returncode==expected and before==after,rec
run('baseline',0)
p=F/'payload/math-note.md';original=p.read_bytes();p.write_bytes(original+b'changed\n');run('changed payload',1);p.write_bytes(original)
p.unlink();run('missing payload',1);p.write_bytes(original)
p=F/'.hidden-extra';p.write_text('extra');run('hidden extra',1);p.unlink()
p=F/'empty-extra';p.mkdir();run('empty directory extra',1);p.rmdir()
hs=anchors.copy();hs[1]='0'*64;run('wrong detached manifest',1,hs)
p=F/'REPORT.md';original=p.read_bytes();p.write_bytes(original+b'changed\n');run('changed outside report',1);p.write_bytes(original)
run('restored baseline',0)
(R/'receipts/copied-controls.json').write_text(json.dumps({'scope':'Three original payload copies; eight artifact-only controls. No original mathematical/source bodies modified.','fixture_detached_anchors':dict(zip(E,anchors)),'results':results},indent=2)+'\n')
print('Eight copied-fixture controls behaved as expected; each verifier invocation preserved fixture bytes/membership/modes/links.')
