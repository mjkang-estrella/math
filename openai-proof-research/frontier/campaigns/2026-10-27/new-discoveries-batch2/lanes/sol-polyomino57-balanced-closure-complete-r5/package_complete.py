from pathlib import Path
import json,hashlib,zipfile,shutil,re,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(90,95));signal.alarm(120)
L=Path(__file__).resolve().parent;W=L/'work'
assert (W/'CompleteEndpoint.olean').exists(), 'Closed endpoint must compile before final packaging'
mods=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 p=W/(m+'.lean');assert p.exists(),m
 for dep in re.findall(r'^import (\S+)',p.read_text(),re.M):
  if (W/(dep+'.lean')).exists():visit(dep)
 mods.append(m)
visit('CompleteEndpoint')
for file,h in json.loads((L/'input-hashes.json').read_text()).items():assert hashlib.file_digest(Path(file).open('rb'),'sha256').hexdigest()==h
for file,h in json.loads((L/'data-input-hashes.json').read_text()).items():assert hashlib.file_digest((L.parent/'sol-polyomino57-full-closure-formal-r4'/file).open('rb'),'sha256').hexdigest()==h
frozen={}
for lane,archive in [('sol-polyomino57-efficient-certificate-r2','source-only-certificate.zip'),('sol-polyomino57-full-closure-formal-r4','source-only-r4.zip')]:
 with zipfile.ZipFile(L.parent/lane/archive) as z:
  for file in z.namelist():
   if file.startswith('formal/') and file.endswith('.lean'):frozen[Path(file).stem]=hashlib.sha256(z.read(file)).hexdigest()
for m in mods:
 if m in frozen:assert hashlib.file_digest((W/(m+'.lean')).open('rb'),'sha256').hexdigest()==frozen[m],m

D=L/'delivery'
assert D.parent==L and D.name=='delivery'
if D.exists():shutil.rmtree(D)
D.mkdir();F=D/'formal';F.mkdir()
for m in mods:
 s=(W/(m+'.lean')).read_text()
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',s),m
 shutil.copyfile(W/(m+'.lean'),F/(m+'.lean'))
audit_template=(W/'ClosureAudit.lean').read_text();tail=audit_template[audit_template.index('import Lean'):]
audits=[]
for start in range(0,len(mods),16):
 group=mods[start:start+16];name=f'OriginAudit{start//16:04d}';audits.append(name)
 a=re.sub(r'  let mods := #\[[^\n]+', '  let mods := #['+', '.join('`'+m for m in group)+']',tail)
 a=a.replace('"dependencies.txt"','"'+name+'-dependencies.txt"')
 a=a.replace('set_option autoImplicit false','set_option maxRecDepth 65536\nset_option maxHeartbeats 10000000\nset_option autoImplicit false')
 (F/(name+'.lean')).write_text('\n'.join('import '+m for m in group)+'\n'+a)
for f in ['pins.json','run.py','input-hashes.json','data-input-hashes.json','fresh_replay.py','provenance.json','resources.md','verification-instructions.md']:shutil.copyfile(L/f,D/f)
(D/'modules.json').write_text(json.dumps(mods+audits,indent=2))
(D/'proof-modules.json').write_text(json.dumps(mods,indent=2))
manifest={str(p.relative_to(D)):hashlib.file_digest(p.open('rb'),'sha256').hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest.json'}
(D/'manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
out=L/'source-only-complete-r5.zip'
with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(D.rglob('*')):
  if p.is_file():
   info=zipfile.ZipInfo(str(p.relative_to(D)),(2026,10,27,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o644<<16;z.writestr(info,p.read_bytes())
(L/'archive.json').write_text(json.dumps(dict(sha256=hashlib.file_digest(out.open('rb'),'sha256').hexdigest(),modules=len(mods),audits=len(audits)),indent=2))
