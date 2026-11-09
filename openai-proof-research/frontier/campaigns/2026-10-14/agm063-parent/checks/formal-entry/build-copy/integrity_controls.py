#!/usr/bin/env python3
"""Test the actual read-only verifier on an isolated package fixture.
Copyright 2026 Myeongjin Kang. MIT. Does not certify mathematical content.
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent

def seal(root):
    files=[]; dirs=[]
    for p in sorted(root.rglob('*')):
        name=p.relative_to(root).as_posix()
        if p.is_dir(): dirs.append(name)
        elif name!='output-manifest.json':
            data=p.read_bytes()
            files.append({'path':name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
    manifest={'schema':'AGM063-scoped-formal-v1','full_AGM063_theorem_formalized':False,
              'independent_audit':False,'files':files,'directories':dirs}
    raw=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode()
    (root/'output-manifest.json').write_bytes(raw)
    return hashlib.sha256(raw).hexdigest()

def main():
    # Enumerate before creating the fixture to avoid recursion.
    entries=[p for p in HERE.iterdir() if p.name not in {'output-manifest.json','__pycache__'}]
    rows=[]
    with tempfile.TemporaryDirectory(prefix='.integrity-',dir=HERE) as td:
        root=Path(td)/'fixture'; root.mkdir()
        for p in entries:
            if p.is_dir(): shutil.copytree(p,root/p.name)
            else: shutil.copy2(p,root/p.name)
        anchor=seal(root)
        def check(name,digest,wanted):
            run=subprocess.run([sys.executable,'-B',str(HERE/'verify.py'),'--root',str(root),'--anchor',digest],text=True,capture_output=True)
            assert (run.returncode==0)==wanted,(name,run.stdout,run.stderr)
            rows.append({'name':name,'exit_code':run.returncode,'stdout':run.stdout,'stderr':run.stderr})
        check('exact-fixture',anchor,True)
        check('wrong-external-anchor','0'*64,False)
        path=root/'AGM063.lean'; data=path.read_bytes()
        path.write_bytes(data+b'\n');check('changed-source',anchor,False);path.write_bytes(data)
        path.unlink();check('missing-source',anchor,False);path.write_bytes(data)
        extra=root/'extra.txt';extra.write_text('extra');check('extra-payload',anchor,False);extra.unlink()
        path.unlink();path.symlink_to(HERE/'AGM063.lean');check('symlink-source',anchor,False);path.unlink();path.write_bytes(data)
        check('restored-exact-fixture',anchor,True)
    result={'meaning':'Pre-seal fixture tests of actual verifier; final package anchor is supplied externally.',
            'fixture_anchor':anchor,'verifier_sha256':hashlib.sha256((HERE/'verify.py').read_bytes()).hexdigest(),
            'rows':rows,'result':'PASS_INTEGRITY_CONTROLS_ONLY'}
    (HERE/'validation/integrity-controls.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Integrity controls: two positive and five negative checks passed.')

if __name__=='__main__': main()
