#!/usr/bin/env python3
"""Require deliberate statement/definition corruptions to fail fresh compilation."""
import json, os, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PACKAGES=ROOT.parents[1]/'2026-10-14/formal/.lake/packages'
LEAN='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
pins=json.loads((ROOT/'formal/pins.json').read_text())
names=['mathlib',*pins['dependencies']]
env=dict(os.environ,LEAN_PATH=os.pathsep.join(str(PACKAGES/n/'.lake/build/lib/lean') for n in names))
source=(ROOT/'formal/ShuffleQuadratic.lean').read_text()
mutations={
    'wrong_eigenvalue': ('= (1/4 : ℝ) • quadraticVector n', '= (1/8 : ℝ) • quadraticVector n'),
    'wrong_denominator': ('(2 : ℝ)^(i.val+1)', '(2 : ℝ)^(i.val+2)'),
    'nonzero_at_two': ('(hn : 3 ≤ n)', '(hn : 2 ≤ n)'),
}
reports={}
for name,(old,new) in mutations.items():
    assert old in source
    folder=ROOT/'build/mutations'/name
    folder.mkdir(parents=True,exist_ok=True)
    path=folder/'ShuffleQuadratic.lean'
    path.write_text(source.replace(old,new))
    run=subprocess.run([LEAN,'-DwarningAsError=true',str(path)],cwd=folder,env=env,text=True,capture_output=True)
    (folder/'compile.log').write_text(run.stdout+run.stderr)
    assert run.returncode != 0, name
    assert 'error' in run.stdout+run.stderr, name
    reports[name]={'exit_code':run.returncode,'status':'REJECTED'}
(ROOT/'build/mutation-check.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps(reports,indent=2))
