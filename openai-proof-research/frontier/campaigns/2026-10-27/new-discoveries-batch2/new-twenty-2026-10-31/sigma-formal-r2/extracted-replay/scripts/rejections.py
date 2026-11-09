#!/usr/bin/env python3
"""Three expected elaboration failures; none claims an exhaustive test."""
from pathlib import Path
import os,sys,json,subprocess
r=Path(__file__).resolve().parent.parent
os.chdir(r)
pins=json.loads((r/'pins.json').read_text());base=Path(pins['cache'])
env={'PATH':'/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:/usr/bin:/bin','LEAN_PATH':':'.join([str(r)]+[str(d/'.lake/build/lib/lean') for d in sorted(base.iterdir()) if d.is_dir()]),'MALLOC_ARENA_MAX':'2','LEAN_NUM_THREADS':'1','LANG':'C.UTF-8'}
cases={
 'ordered-factor': 'example : Sigma365710.sigmaT (Sigma365710.completeBipartite 4 1) = 24 := by decide',
 'noninduced-path': 'example : (2 : ℤ) ≤ Sigma365710.deficit (Sigma365710.completeBipartite 4 2) := by decide',
 'omit-triangle-free': 'example : (0 : ℤ) ≤ Sigma365710.deficit (⊤ : SimpleGraph (Fin 3)) := by decide',
}
logs=r/'replay-logs';logs.mkdir(exist_ok=True)
results=[]
for label,body in cases.items():
 f=r/'RejectedMutation.lean'
 f.write_text('import Sigma.Endpoint\n'+body+'\n')
 try:
  p=subprocess.run([sys.executable,'scripts/capped.py','lean','-j1','-DwarningAsError=true',f.name],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  (logs/('reject-'+label+'.log')).write_text(p.stdout)
  ok=p.returncode==1 and 'Tactic `decide` proved that the proposition' in p.stdout
  results.append({'case':label,'body':body,'exit':p.returncode,'expected_rejection':ok})
 finally: f.unlink()
(r/'rejection-results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
assert all(x['expected_rejection'] for x in results)
