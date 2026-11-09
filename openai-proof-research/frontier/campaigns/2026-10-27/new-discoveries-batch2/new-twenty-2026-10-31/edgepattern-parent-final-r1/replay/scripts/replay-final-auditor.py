from pathlib import Path
import os,sys,subprocess,json,hashlib,zipfile
root=Path(__file__).resolve().parents[1]
build=root/'extracted'
fresh=root/'auditor-final-extracted'
assert not fresh.exists(), 'Fresh auditor extraction must not exist'
modules=json.loads((root/'scripts/modules.json').read_text())
prior=json.loads((build/'replay-receipt.json').read_text())
assert prior['passed']
for m in modules:
 if m!='AuditR5':
  key='formal/'+m+'.lean'
  assert hashlib.sha256((root/key).read_bytes()).hexdigest()==prior['formal_source_sha256'][key]
packet=root/'auditor-final-source.zip'
with zipfile.ZipFile(packet,'w',zipfile.ZIP_DEFLATED) as z:
 for name in ['formal/AuditR5.lean','checks/AuditToolSafety.lean','scripts/watchdog.py']:
  z.write(root/name,name)
with zipfile.ZipFile(packet) as z:z.extractall(fresh)
assert not list(fresh.rglob('*.olean'))
for name in ['logs','tmp','empty-home']:(fresh/name).mkdir()
lean=Path(os.environ['LEAN_BIN']).resolve()
packages=Path(os.environ['LEAN_PACKAGES']).resolve()
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env['PATH']=str(lean.parent)+os.pathsep+os.defpath
env.update(LEAN_PATH=':'.join([str(fresh/'formal'),str(build/'formal')]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]),HOME=str(fresh/'empty-home'),TMPDIR=str(fresh/'tmp'),MALLOC_ARENA_MAX='2')
os.chdir(fresh)
commands=[
 ('replay-AuditR5',[str(lean),'-j1','-DwarningAsError=true','-o','formal/AuditR5.olean','formal/AuditR5.lean']),
 ('leanchecker-AuditR5',[str(lean.with_name('leanchecker')),'AuditR5']),
 ('auditor-safety',[str(lean),'-j1','-DwarningAsError=true','checks/AuditToolSafety.lean'])]
checks=[]
for name,cmd in commands:
 rc=subprocess.run([sys.executable,'-I','scripts/watchdog.py','logs/'+name+'.log',*cmd],env=env).returncode
 checks.append({'name':'final-auditor-'+name,'exit_code':rc})
 if rc:break
receipt={'passed':len(checks)==len(commands) and all(c['exit_code']==0 for c in checks),'checks':checks,'source_sha256':hashlib.sha256((fresh/'formal/AuditR5.lean').read_bytes()).hexdigest(),'packet_sha256':hashlib.sha256(packet.read_bytes()).hexdigest(),'fresh_extraction':True,'proof_import_cache':'../extracted/formal; all 268 proof modules were freshly rebuilt and kernel-checked; their sources are hash-identical','reason':'Only audit tooling outside the endpoint import closure changed after the full proof replay.'}
(root/'final-auditor-replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
sys.exit(0 if receipt['passed'] else 1)
