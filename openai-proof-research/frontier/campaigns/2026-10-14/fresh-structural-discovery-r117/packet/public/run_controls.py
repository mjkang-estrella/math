#!/usr/bin/env python3
"""Copied final-anchor integrity controls. Never modifies the original packet.
Temporary files are confined to the caller-specified owned scratch directory.
Authenticity and mathematical validity remain outside this diagnostic.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def snapshot(root):
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(root.rglob('*')) if p.is_file()}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet', type=Path, required=True)
    ap.add_argument('--scratch', type=Path, required=True)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    a = ap.parse_args()
    original = a.packet.resolve()
    scratch = a.scratch.resolve()
    if scratch == original or original in scratch.parents:
        ap.error('scratch must be outside original packet')
    scratch.mkdir(parents=True, exist_ok=True)
    before = snapshot(original)
    trusted = original / 'public/verify.py'
    rows = []
    with tempfile.TemporaryDirectory(prefix='copied-controls-', dir=scratch) as td:
        base = Path(td)
        names = ['clean', 'wrong_finalhash', 'wrong_reporthash', 'missing_finalhash',
                 'missing_reporthash', 'changed_report', 'missing_payload', 'extra_file',
                 'extra_directory', 'symlink', 'hardlink', 'changed_source',
                 'self_resealed_tamper', 'duplicate_manifest_key']
        for name in names:
            copy = base / name
            shutil.copytree(original, copy)
            fh, rh = a.finalhash, a.reporthash
            if name == 'wrong_finalhash': fh = '0'*64
            if name == 'wrong_reporthash': rh = '0'*64
            if name == 'changed_report':
                with (copy/'public/report.md').open('ab') as f: f.write(b'\nchanged\n')
            if name == 'missing_payload': (copy/'public/automata.md').unlink()
            if name == 'extra_file': (copy/'extra.txt').write_text('extra')
            if name == 'extra_directory': (copy/'extra-empty').mkdir()
            if name == 'symlink': (copy/'extra-link').symlink_to('public/report.md')
            if name == 'hardlink': os.link(copy/'public/report.md', copy/'extra-hardlink')
            if name == 'changed_source':
                source = next((copy/'private/upstream').rglob('*.tex'))
                with source.open('ab') as f: f.write(b'\n%changed\n')
            if name == 'self_resealed_tamper':
                p = copy/'public/report.md'; p.write_bytes(p.read_bytes()+b'\nforged\n')
                m = json.loads((copy/'MANIFEST.json').read_bytes())
                m['files']['public/report.md']={'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
                (copy/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
            if name == 'duplicate_manifest_key':
                p=copy/'MANIFEST.json';s=p.read_text();p.write_text('{"schema":1,'+s[1:])
            cmd=[sys.executable,str(trusted),'--packet',str(copy)]
            if name != 'missing_finalhash':cmd+=['--finalhash',fh]
            if name != 'missing_reporthash':cmd+=['--reporthash',rh]
            p=subprocess.run(cmd,capture_output=True,text=True)
            expected=0 if name=='clean' else (2 if name.startswith('missing_') and name in ['missing_finalhash','missing_reporthash'] else 1)
            if p.returncode != expected:
                raise RuntimeError(name+': unexpected status '+str(p.returncode)+' '+p.stdout+p.stderr)
            rows.append({'case':name,'expected_exit':expected,'observed_exit':p.returncode,
                         'diagnostic':p.stderr.strip().splitlines()[-1] if p.stderr.strip() else 'integrity verified'})
        finite=subprocess.run([sys.executable,str(original/'public/finite_checks.py')],capture_output=True,text=True,check=True)
        expected=json.loads((original/'public/finite-results.json').read_bytes())
        if json.loads(finite.stdout)!=expected:raise RuntimeError('finite replay mismatch')
    after=snapshot(original)
    if before!=after:raise RuntimeError('original packet changed')
    print(json.dumps({'finalhash':a.finalhash,'reporthash':a.reporthash,'cases':rows,
                      'original_unchanged':True,'finite_replay':True,
                      'mathematical_gate':False,'contribution_gate':False},indent=2))


if __name__=='__main__':main()
