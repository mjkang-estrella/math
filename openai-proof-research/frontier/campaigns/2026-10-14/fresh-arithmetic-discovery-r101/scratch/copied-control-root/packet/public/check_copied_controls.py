#!/usr/bin/env python3
"""Bounded integrity controls; writes only root/scratch and a detached receipt.
The original packet, FINAL, REPORT, notes and project inputs are never changed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--root',type=Path,required=True)
p.add_argument('--project',type=Path,required=True)
for n in ['final','manifest','report']:p.add_argument('--'+n+'-sha256',required=True)
a=p.parse_args(); root=a.root.resolve(); clone=root/'scratch/copied-control-root'
if clone.exists() or (root/'integrity-results.json').exists():
    raise SystemExit('refusing to overwrite an existing control run')
clone.mkdir(parents=True)
shutil.copytree(root/'packet',clone/'packet')
shutil.copytree(root/'notes',clone/'notes')
for name in ['FINAL.json','REPORT.md']:shutil.copy2(root/name,clone/name)

def snap(base):
    return {str(x.relative_to(base)):hashlib.sha256(x.read_bytes()).hexdigest()
            for x in base.rglob('*') if x.is_file()}

initial=snap(clone)
base=[sys.executable,'-B',str(root/'packet/public/verify.py'),'--root',str(clone),
      '--project',str(a.project.resolve()),'--final-sha256',a.final_sha256,
      '--manifest-sha256',a.manifest_sha256,'--report-sha256',a.report_sha256]
cases=[]
def run(name,expected,cmd=None):
    z=subprocess.run(cmd or base,capture_output=True,text=True)
    cases.append({'case':name,'exit':z.returncode,'expected_exit':expected,
                  'expected_result':z.returncode==expected,'stdout':z.stdout,'stderr':z.stderr})
run('baseline',0)
wrong=base.copy();wrong[wrong.index('--final-sha256')+1]='0'*64
run('wrong detached FINAL',1,wrong)
missing=base.copy();i=missing.index('--manifest-sha256');del missing[i:i+2]
run('missing detached MANIFEST',2,missing)
for name,path in [('changed public proof',clone/'packet/public/author-proof.md'),
                  ('changed pinned source',next((clone/'packet/private/upstream').rglob('local.tex')))]:
    old=path.read_bytes();path.write_bytes(old+b'\ntamper\n')
    run(name,1);path.write_bytes(old)
extra=clone/'packet/public/extra-unregistered.txt';extra.write_text('tamper')
run('extra payload member',1);extra.unlink()
assert snap(clone)==initial,'copied inputs not restored'
original=base.copy();original[original.index('--root')+1]=str(root)
run('original after controls',0,original)
receipt={'artifact_controls_only':True,'all_expected':all(x['expected_result'] for x in cases),
         'copied_inputs_restored':True,'cases':cases,
         'anchors':{'final':a.final_sha256,'manifest':a.manifest_sha256,'outside_report':a.report_sha256},
         'limits':'No mathematical review, malicious-resealing test or comprehensive syscall-denial claim. Receipt and disposable fixture are outside the sealed packet.'}
(root/'integrity-results.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'all_expected':receipt['all_expected'],'cases':len(cases),
                  'receipt_sha256':hashlib.sha256((root/'integrity-results.json').read_bytes()).hexdigest()}))
if not receipt['all_expected']:sys.exit(1)
