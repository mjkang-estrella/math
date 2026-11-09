#!/usr/bin/env python3
"""Run from a fresh extraction; no pre-existing compiled local files allowed."""
import os,sys,subprocess,hashlib,json,shutil
from pathlib import Path
root=Path(__file__).resolve().parents[1]
lean=Path(os.environ['LEAN_BIN']).resolve();packages=Path(os.environ['LEAN_PACKAGES']).resolve()
for suffix in ('*.olean','*.ilean','*.ir'):
 if list(root.rglob(suffix)):sys.exit('refusing existing local compiled files: '+suffix)
if (root/'build').exists():sys.exit('refusing existing build directory')
build=root/'build';build.mkdir(); logs=root/'replay-logs';logs.mkdir(exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(build)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()]);env['MALLOC_ARENA_MAX']='2';env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','');env['LEAN_NUM_THREADS']='1'
# Sanitize all local source text before replay. No proof holes or forbidden evaluators.
import re
for p in (root/'formal').glob('*.lean'):
 text=p.read_text()
 code=re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S)
 if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',code):
  # The audit compares flag names and logs them, but introduces none.
  if p.name!='Audit.lean':sys.exit('forbidden token in '+str(p))
for name in ['SourceContact','QuadraticBranches','ExactOrders','Audit']:
 shutil.copyfile(root/'formal'/f'{name}.lean',build/f'{name}.lean')
def call(label,cmd,expected=0):
 log=logs/(label+'.log')
 cp=subprocess.run([sys.executable,'-I','-B',str(root/'scripts/capped.py'),str(log)]+cmd,cwd=build,env=env,stdout=subprocess.DEVNULL)
 if (cp.returncode==0)!=(expected==0):sys.exit('unexpected result for '+label+'; see '+str(log))
for name in ['SourceContact','QuadraticBranches','ExactOrders','Audit']:
 call('lean-'+name,[str(lean),'-j1','-DwarningAsError=true','-o',name+'.olean',name+'.lean'])
 # leanchecker performs a separate kernel check using the same import path.
 call('checker-'+name,[str(lean.with_name('leanchecker')),name])
# Negative controls are independent failing assertions, not accepted certificate declarations.
controls={
 'false-square-root':'import QuadraticBranches\nexample : (1:ℂ)^2 = 2 := by norm_num\n',
 'wrong-residual':'import ExactOrders\nopen ContactPilot\nexample : H 0 = 0 := by norm_num [H]\n',
 'wrong-contact':'import SourceContact\nopen ContactPilot\nexample : HasZeroSetContact (fun _ _ => 1) (-1) 1 2 := by\n  unfold HasZeroSetContact\n  simp\n',
}
for name,text in controls.items():
 (build/(name+'.lean')).write_text(text)
 call('negative-'+name,[str(lean),'-j1','-DwarningAsError=true',name+'.lean'],expected=1)
(logs/'complete.json').write_text(json.dumps({'status':'PASS','modules':4,'negative_controls':len(controls),'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/'formal').glob('*.lean')}},indent=2)+'\n')
print('PASS: strict build, leanchecker, declaration audit and three negative controls')
