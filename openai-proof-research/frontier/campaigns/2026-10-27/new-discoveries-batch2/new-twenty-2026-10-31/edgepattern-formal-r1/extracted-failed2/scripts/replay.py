#!/usr/bin/env python3
"""Portable source-only replay; run from an extracted packet's root."""
from pathlib import Path
import os,sys,subprocess,json,hashlib
root=Path(__file__).resolve().parents[1];os.chdir(root)
if any(root.rglob('*.olean')):
 raise SystemExit('REFUSED: existing .olean files; extract a fresh source-only packet')
lean=Path(os.environ['LEAN_BIN']).resolve(); packages=Path(os.environ['LEAN_PACKAGES']).resolve()
paths=[str(root/'formal')]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
# Ignore inherited Lean search paths, user Lake configuration and project variables.
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env.update(LEAN_PATH=':'.join(paths),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1',HOME=str(root/'empty-home'),TMPDIR=str(root/'tmp'))
for p in ['empty-home','tmp','logs']:(root/p).mkdir(exist_ok=True)
commands=[]
for m in ['Definitions','Concrete','Canonical','Separation','Invariance','Audit']:
 commands.append(('replay-'+m,[str(lean),'-j1','-DwarningAsError=true','-o','formal/'+m+'.olean','formal/'+m+'.lean']))
for m in ['Definitions','Concrete','Canonical','Separation','Invariance']:
 commands.append(('leanchecker-'+m,[str(lean.with_name('leanchecker')),m]))
receipts=[]
for name,cmd in commands:
 rc=subprocess.run([sys.executable,'-I','scripts/watchdog.py','logs/'+name+'.log',*cmd],env=env).returncode
 receipts.append({'name':name,'exit_code':rc})
 if rc:break
(root/'replay-receipt.json').write_text(json.dumps({'checks':receipts,'passed':all(x['exit_code']==0 for x in receipts) and len(receipts)==len(commands),'endpoint':'PARTIAL ONLY; no theorem refuting Conjecture2'},indent=2)+'\n')
sys.exit(0 if len(receipts)==len(commands) and all(x['exit_code']==0 for x in receipts) else 1)
