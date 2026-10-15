#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Rerun the two finite diagnostics and record their actual execution."""
import hashlib,json,os,subprocess,sys,time
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);runs=[]
 for script,output in [('tensor_controls.py','checks.json'),('projection_controls.py','projection-checks.json')]:
  start=time.monotonic();cmd=[sys.executable,'-B',script]
  proc=subprocess.run(cmd,cwd=ROOT,env=env,text=True,capture_output=True)
  row={'command':cmd,'script_sha256':digest(ROOT/script),'exit_code':proc.returncode,'elapsed_seconds':round(time.monotonic()-start,6),'stdout':proc.stdout,'stderr':proc.stderr,'assertions_enabled':True}
  if proc.returncode==0:row['output_sha256']=digest(ROOT/output)
  runs.append(row)
  if proc.returncode:break
 report={'run_utc':datetime.now(timezone.utc).isoformat(),'python_version':sys.version,'scope':'finite exact diagnostics only; not independent proof or contribution acceptance','runs':runs,'passed':len(runs)==2 and all(r['exit_code']==0 for r in runs)}
 if '--record' in sys.argv:
  (ROOT/'check-run.json').write_text(json.dumps(report,indent=2)+'\n')
 elif (ROOT/'check-run.json').exists():
  sealed=json.loads((ROOT/'check-run.json').read_text())
  assert [(r['script_sha256'],r.get('output_sha256')) for r in runs]==[(r['script_sha256'],r.get('output_sha256')) for r in sealed['runs']], 'Frozen diagnostic inputs or outputs changed'
 print(json.dumps({'passed':report['passed'],'checks':[{k:r[k] for k in ['command','exit_code','elapsed_seconds','output_sha256'] if k in r} for r in runs]},indent=2))
 if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
