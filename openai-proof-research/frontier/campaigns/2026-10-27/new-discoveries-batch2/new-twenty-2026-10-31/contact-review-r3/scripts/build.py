from pathlib import Path
import os,sys,zipfile,shutil,re,subprocess,json
r=Path(__file__).resolve().parents[1]; src=r.parent/'contact-formal-r6'; x=r/'extracted'; x.mkdir()
with zipfile.ZipFile(src/'contact-r6-source.zip') as z:
 for i in z.infolist():
  assert not Path(i.filename).is_absolute() and '..' not in Path(i.filename).parts
 z.extractall(x)
f=next(x.rglob('RefutationLocal.lean')).parent
build=x/'review-build'; build.mkdir()
seen=[]
def visit(n):
 if n in seen:return
 for dep in re.findall(r'^import (\w+)',(f/(n+'.lean')).read_text(),re.M):
  if (f/(dep+'.lean')).exists():visit(dep)
 seen.append(n)
visit('RefutationLocal')
(r/'closure.json').write_text(json.dumps(seen,indent=2))
p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
l='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
e=os.environ.copy();e.update(LEAN_PATH=':'.join([str(build)]+[str(t/'.lake/build/lib/lean') for t in sorted(p.iterdir()) if t.is_dir()]),TMPDIR=str(r/'tmp'),XDG_CACHE_HOME=str(r/'tmp/cache'),MALLOC_ARENA_MAX='2',LEAN_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
for n in seen:shutil.copyfile(f/(n+'.lean'),build/(n+'.lean'))
def call(label,cmd):
 subprocess.run([sys.executable,'-I',str(r/'scripts/capped.py'),str(r/'logs'/(label+'.log'))]+cmd,env=e,cwd=build,check=True)
for n in seen:call(n,[l,'-j1','-M3500','-DwarningAsError=true','-o',n+'.olean',n+'.lean'])
call('leanchecker-RefutationLocal',[str(Path(l).with_name('leanchecker')),'RefutationLocal'])
(build/'PrintAxioms.lean').write_text('import RefutationLocal\n#print axioms ContactPilot.refutationLocal\n#print axioms ContactPilot.local_contact_unique\n#print axioms ContactPilot.bidisk_local_contact_six\n')
call('axioms',[l,'-j1','-M3500','-DwarningAsError=true','PrintAxioms.lean'])
print('COMPLETE',len(seen))
