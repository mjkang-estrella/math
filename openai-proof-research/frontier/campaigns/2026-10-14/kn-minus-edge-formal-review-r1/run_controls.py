#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Independent controls driver."""
from pathlib import Path
import json, os, re, subprocess, shutil, hashlib
HERE=Path(__file__).resolve().parent
r=json.loads((HERE/'build-receipt.json').read_text())
env=os.environ.copy(); env['LEAN_PATH']=r['LEAN_PATH']; env['PYTHONDONTWRITEBYTECODE']='1'
shutil.copyfile(HERE/'ReviewControls.lean',HERE/'build/ReviewControls.lean')
steps=[('review-controls',['-o','ReviewControls.olean','ReviewControls.lean'])]
names=re.findall(r'^theorem (\w+)',(HERE/'ReviewControls.lean').read_text(),re.M)
(HERE/'build/ReviewQueries.lean').write_text('import ReviewControls\n'+'\n'.join('#check @IndependentReview.'+n+'\n#print axioms IndependentReview.'+n for n in names)+'\n')
steps.append(('review-control-types-axioms',['ReviewQueries.lean']))
result={'source_sha256':hashlib.sha256((HERE/'ReviewControls.lean').read_bytes()).hexdigest(),'theorems':names,'runs':[]}
for label,args in steps:
    p=subprocess.run([r['compiler_realpath'],*args],cwd=HERE/'build',env=env,capture_output=True,text=True)
    (HERE/'logs'/f'{label}.stdout').write_text(p.stdout); (HERE/'logs'/f'{label}.stderr').write_text(p.stderr)
    result['runs'].append({'label':label,'exit_code':p.returncode,'command':[r['compiler_realpath'],*args]})
    (HERE/'controls-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(label,p.returncode,flush=True)
    if p.returncode: print(p.stdout,p.stderr); raise SystemExit(p.returncode)
result['status']='PASS'; (HERE/'controls-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
