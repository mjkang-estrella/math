#!/usr/bin/env python3
"""Mutate disposable copies under private/; never alter the sealed public files."""
import argparse, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

ap=argparse.ArgumentParser();ap.add_argument('--expected-manifest-sha256',required=True);args=ap.parse_args()
root=Path(__file__).absolute().parent
cases=['clean','changed_payload','extra_directory','symlink_payload','hardlink_payload','missing_payload','changed_manifest','wrong_external_anchor']
results=[]
with tempfile.TemporaryDirectory(prefix='negative-controls-',dir=root/'private') as temp:
    base=Path(temp)
    for case in cases:
        fixture=base/case;fixture.mkdir()
        for p in root.iterdir():
            if p.is_file():shutil.copyfile(p,fixture/p.name)
        target=fixture/'structured-metric-deflation-obstruction.md'
        anchor=args.expected_manifest_sha256
        if case=='changed_payload':target.write_bytes(target.read_bytes()+b'\nchanged\n')
        elif case=='extra_directory':(fixture/'extra').mkdir()
        elif case=='symlink_payload':target.unlink();target.symlink_to(fixture/'README.md')
        elif case=='hardlink_payload':
            twin=base/(case+'-twin');shutil.copyfile(target,twin);target.unlink();os.link(twin,target)
        elif case=='missing_payload':target.unlink()
        elif case=='changed_manifest':
            p=fixture/'MANIFEST.json';p.write_bytes(p.read_bytes()+b' ')
        elif case=='wrong_external_anchor':anchor='0'*64
        result=subprocess.run([sys.executable,'-B',str(fixture/'verify.py'),'--expected-manifest-sha256',anchor],capture_output=True,text=True)
        accepted=result.returncode==0
        if accepted!=(case=='clean'):raise AssertionError(case+': '+result.stdout+result.stderr)
        results.append({'case':case,'accepted':accepted,'expected':case=='clean'})
print(json.dumps({'status':'PASS_NEGATIVE_CONTROLS','cases':results,'limits':'Integrity negative controls only; no mathematical proof verdict or review.'},sort_keys=True,indent=2))
