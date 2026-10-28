#!/usr/bin/env python3
from pathlib import Path
import os, subprocess, sys, json, hashlib, datetime
lane=Path(__file__).resolve().parents[1]
base=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[base/'.lake/build/lib/lean',*sorted((base/'.lake/packages').glob('*/.lake/build/lib/lean'))]))
p=subprocess.run([lean,str(lane/'formal/TwoLevel.lean')],cwd=lane,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(lane/'formal/replay.log').write_text(p.stdout)
print(p.stdout)
forbidden=['sorryAx', 'declaration uses', 'error:']
strict_ok=p.returncode==0 and not any(w in p.stdout for w in forbidden)
source=(lane/'formal/TwoLevel.lean').read_bytes()
report={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'lean':lean,'mathlib_revision_user_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'file':'formal/TwoLevel.lean','sha256':hashlib.sha256(source).hexdigest(),
 'returncode':p.returncode,'strict_ok':strict_ok,
 'scope':'Initial lemmas only; no full source-inner-product theorem',
 'axiom_lines':[x for x in p.stdout.splitlines() if 'depends on axioms:' in x]}
(lane/'formal/verification.json').write_text(json.dumps(report,indent=2)+'\n')
sys.exit(0 if strict_ok else 1)
