#!/usr/bin/env python3
"""Integrity controls on one disposable local copy, never on originals.

Run only inside the assigned r135 root, after the single final seal. The local
ANCHORS.json is merely supplied test data, not an independent trust root.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
assert root.name == 'fresh-analytic-discovery-r135'
anchors = json.loads((root / 'ANCHORS.json').read_text())
work = root / 'copied-controls-private'
if work.exists():
    raise RuntimeError('refusing to reuse existing control directory')
work.mkdir()
shutil.copytree(root / 'packet', work / 'packet')
for name in ('FINAL.md', 'REPORT.md'):
    shutil.copy2(root / name, work / name)
verifier = root / 'packet/public/verify_packet.py'
args = [sys.executable, str(verifier), str(work),
        '--manifest-sha', anchors['manifest'], '--final-sha', anchors['final'],
        '--report-sha', anchors['report']]
rows = []

def run(label, expected):
    p = subprocess.run(args, capture_output=True, text=True)
    rows.append({'control': label, 'expected_exit': expected,
                 'actual_exit': p.returncode, 'verifier_output': json.loads(p.stdout)})
    if p.returncode != expected:
        raise RuntimeError(f'control failed: {label}')

try:
    run('unchanged copied baseline', 0)
    p = work / 'packet/public/author-proof.md'; old = p.read_bytes()
    p.write_bytes(old + b'\nCONTROL ONLY\n')
    run('altered public proof rejected', 1); p.write_bytes(old)
    p.unlink(); run('missing public proof rejected', 1); p.write_bytes(old)
    extra = work / 'packet/unlisted-control.txt'; extra.write_text('control')
    run('unlisted file rejected', 1); extra.unlink()
    p = work / 'packet/public/control-link'; p.symlink_to('author-proof.md')
    run('symlink rejected', 1); p.unlink()
    for name in ('FINAL.md', 'REPORT.md', 'packet/MANIFEST.json'):
        p = work / name; old = p.read_bytes(); p.write_bytes(old + b'\n')
        run('altered detached ' + name + ' rejected', 1); p.write_bytes(old)
    run('restored copied baseline', 0)
    receipt = {'controls': rows, 'all_expected_outcomes_observed': True,
               'mutation_target': 'disposable copied-controls-private only',
               'limits': 'artifact controls only, not mathematical tests'}
    (root / 'copied-controls.json').write_text(json.dumps(receipt, indent=2) + '\n')
finally:
    shutil.rmtree(work)
print(json.dumps({'controls': len(rows), 'receipt': 'copied-controls.json'}))
