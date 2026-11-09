#!/usr/bin/env python3
"""Build a separate byte copy without any pre-existing project oleans."""
import hashlib, json, shutil, subprocess, datetime
from pathlib import Path
lane=Path(__file__).resolve().parents[1]
fresh=lane/'replay'/'fresh'
fresh.mkdir(exist_ok=False)
(fresh/'formal').mkdir()
(fresh/'logs').mkdir()
files=['BinomialMoments.lean','FiniteTransform.lean','BinomialOddSum.lean','Audit.lean','run_lean.py','guard.py']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source_hashes={}
for name in files:
    src=lane/'formal'/name; dst=fresh/'formal'/name
    shutil.copyfile(src,dst)
    assert sha(src)==sha(dst)
    source_hashes['formal/'+name]=sha(dst)
assert not list(fresh.rglob('*.olean'))
steps=[]
for name in ['BinomialMoments','FiniteTransform','BinomialOddSum','Audit']:
    cmd=['python','formal/guard.py','python','formal/run_lean.py','-j1','-M4096']
    if name!='Audit': cmd+=['-o',f'formal/{name}.olean']
    cmd+=[f'formal/{name}.lean']
    log=fresh/'logs'/f'{name}.log'
    with log.open('w') as f: p=subprocess.run(cmd,cwd=fresh,stdout=f,stderr=subprocess.STDOUT)
    lines=log.read_text().splitlines()
    guard=json.loads(lines[-1])
    step={'command':cmd,'cwd':str(fresh),'exit_code':p.returncode,'log':str(log.relative_to(lane)),
          'log_sha256':sha(log),'guard':guard}
    steps.append(step)
    print(json.dumps({'module':name,'exit_code':p.returncode,'peak_rss_kib':guard['peak_rss_kib']}),flush=True)
    if p.returncode: break
matched=all(sha(lane/p)==h==sha(fresh/p) for p,h in source_hashes.items())
receipt={'status':'PASS' if len(steps)==4 and all(s['exit_code']==0 for s in steps) and matched else 'FAIL',
 'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'method':'Fresh isolated source extraction; no initial project oleans; separate sequential kernel elaborations; same solo implementation agent, not a separate reviewer.',
 'initial_project_oleans':[], 'original_and_copy_hashes_match_before_and_after':matched,
 'source_sha256':source_hashes,'steps':steps}
(lane/'replay'/'fresh-replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
raise SystemExit(0 if receipt['status']=='PASS' else 1)
