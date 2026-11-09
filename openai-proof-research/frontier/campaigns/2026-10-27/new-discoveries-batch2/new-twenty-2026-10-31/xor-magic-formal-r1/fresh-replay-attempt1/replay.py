#!/usr/bin/env python3
from pathlib import Path
import os,sys,json,subprocess,hashlib
root=Path(__file__).resolve().parent
if list(root.rglob('*.olean')) or list(root.rglob('*.olean.*')):
 raise SystemExit('Refusing a packet containing existing oleans')
lean=Path(os.environ['LEAN_BIN']).resolve(); packages=Path(os.environ['LEAN_PACKAGES']).resolve()
if not lean.is_file() or not packages.is_dir(): raise SystemExit('Invalid LEAN_BIN or LEAN_PACKAGES')
for dirname in ['logs','tmp','home']: (root/dirname).mkdir(exist_ok=True)
# All inherited Lean configuration, plugin paths and user environment are discarded.
os.environ.clear()
os.environ.update(PATH=str(lean.parent)+':/usr/bin:/bin',HOME=str(root/'home'),TMPDIR=str(root/'tmp'),MALLOC_ARENA_MAX='2',LEAN_PATH=':'.join([str(root/'formal')]+[str(x/'.lake/build/lib/lean') for x in sorted(packages.iterdir()) if x.is_dir()]),LANG='C.UTF-8')
os.chdir(root)
version=subprocess.check_output([str(lean),'--version'],text=True)
(root/'logs/toolchain.txt').write_text(version)
if '4.34.1' not in version or '5045d0056413266e57c625dcd7c365b10e377c52' not in version: raise SystemExit('Wrong Lean toolchain')
manifest=json.loads((root/'source-manifest.json').read_text())
for name,digest in manifest.items():
 if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest: raise SystemExit('Source hash mismatch: '+name)
modules=json.loads((root/'modules.json').read_text())
receipts=[]
def run(name,args,expect_failure=False):
 log=root/'logs'/f'{name}.log'
 code=subprocess.call([sys.executable,'-I',str(root/'tools/bounded.py'),str(log)]+args)
 r=json.loads(Path(str(log)+'.json').read_text());receipts.append(r)
 if expect_failure:
  if code==0 or 'evaluated to `false`' not in log.read_text(): raise SystemExit('Negative control did not fail as expected: '+name)
 elif code: raise SystemExit('Failed: '+name)
for m in modules+['Audit']:
 print('STRICT_BUILD',m,flush=True)
 run(m,[str(lean),'-j1','-DwarningAsError=true','-o',f'formal/{m}.olean',f'formal/{m}.lean'])
for m in modules+['Audit']:
 print('LEANCHECKER',m,flush=True)
 run('leanchecker-'+m,[str(lean.parent/'leanchecker'),'--verbose',m])
for m in ['BadDegree','BadLabel','BadSum']:
 print('NEGATIVE_CONTROL',m,flush=True)
 run(m,[str(lean),'-j1','-DwarningAsError=true',f'negative/{m}.lean'],True)
(root/'logs/replay-receipt.json').write_text(json.dumps({'status':'pass','modules':modules,'audit':True,'leanchecker':True,'negative_controls':['BadDegree','BadLabel','BadSum'],'receipts':receipts},indent=2)+'\n')
print('PARTIAL_PACKET_REPLAY_PASS',flush=True)
