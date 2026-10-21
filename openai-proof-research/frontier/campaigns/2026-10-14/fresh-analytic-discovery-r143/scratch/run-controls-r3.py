#!/usr/bin/env python3
"""Seven bounded copied integrity controls. Run only before the final seal."""
from pathlib import Path
import hashlib, json, shutil, subprocess, sys
r = Path(__file__).resolve().parent.parent
if any((r / n).exists() for n in ['FINAL.md','MANIFEST.json','REPORT.md']):
    raise SystemExit('Refusing to mutate controls after the final seal.')
f = r / 'scratch' / 'control-fixture'
f.mkdir(exist_ok=False)
shutil.copyfile(r / 'DERIVATION-R3.md', f / 'selected-original-prose.md')
(f/'FINAL.md').write_text('Integrity fixture only, not a research handoff.\n')
(f/'REPORT.md').write_text('Selection: DERIVATION-R3.md copied as selected-original-prose.md.\n')
sha=lambda b:hashlib.sha256(b).hexdigest()
b=(f/'selected-original-prose.md').read_bytes()
manifest={'format':'r143-exact-payload-v1','outside_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],
          'files':[{'path':'selected-original-prose.md','size':len(b),'sha256':sha(b)}],
          'scope':'New selected-copy membership; not the original-root manifest.'}
(f/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
anchors={n:sha((f/n).read_bytes()) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
cmd=[sys.executable,str(r/'verify.py'),str(f),'--final-sha256',anchors['FINAL.md'],
     '--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
results=[]
def check(name,want):
    p=subprocess.run(cmd,text=True,capture_output=True)
    assert (p.returncode==0)==want,(name,p.stdout,p.stderr)
    results.append({'case':name,'expected_accept':want,'exit_code':p.returncode,'observed':json.loads(p.stdout)})
check('pristine independently manifested selected copy',True)
for name in ['selected-original-prose.md','FINAL.md','MANIFEST.json','REPORT.md']:
    old=(f/name).read_bytes();(f/name).write_bytes(old+b'\nmutation\n')
    check('detect mutation '+name,False)
    (f/name).write_bytes(old)
(f/'unexpected.txt').write_text('extra member\n')
check('detect added payload member',False)
(f/'unexpected.txt').unlink()
check('restored selected copy',True)
(r/'scratch'/'control-results.json').write_text(json.dumps({'kind':'artifact-only; not mathematical gates',
    'fixture_anchors':anchors,'controls':results},indent=2)+'\n')
print(json.dumps({'controls':len(results),'all_expected_outcomes':True}))
