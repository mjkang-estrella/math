#!/usr/bin/env python3
"""Bounded postseal controls. Mutates only a new scratch/copied-controls tree."""
import argparse
import fnmatch
import json
from pathlib import Path
import shutil
import subprocess
import sys

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--root', type=Path, required=True)
p.add_argument('--final-sha256', required=True)
p.add_argument('--manifest-sha256', required=True)
p.add_argument('--report-sha256', required=True)
a = p.parse_args()
r = a.root.absolute()
assert r.name == 'fresh-arithmetic-discovery-r109'
outside = r / 'scratch/copied-controls'
outside.mkdir(exist_ok=False)
copy = outside / 'packet'
copy.mkdir()
manifest = json.loads((r / 'MANIFEST.json').read_text())
paths = [v['path'] for v in manifest['files']] + ['FINAL.md', 'MANIFEST.json', 'REPORT.md', 'ANCHORS.sha256']
for name in paths:
    assert not any(fnmatch.fnmatch(part.lower(), pat) for part in Path(name).parts for pat in ['*structural*r144*', '*analytic*r138*', '*t185r144-*', '*h138-*'])
    source, target = r / name, copy / name
    assert not source.is_symlink()
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)

base = [sys.executable, '-B', str(r / 'code/verify.py')]
anchor_args = ['--final-sha256', a.final_sha256, '--manifest-sha256', a.manifest_sha256, '--report-sha256', a.report_sha256]
rows = []


def run(label, root, expected, args=None):
    q = subprocess.run(base + ['--root', str(root)] + (anchor_args if args is None else args), capture_output=True, text=True, timeout=30)
    rows.append({'case': label, 'expected_exit': expected, 'actual_exit': q.returncode, 'stdout': q.stdout.strip(), 'stderr': q.stderr.strip()})
    assert q.returncode == expected, label


run('original-before', r, 0)
run('copy-baseline', copy, 0)
target = copy / 'notes/characteristic-feasibility.md'
saved = target.read_bytes()
target.write_bytes(saved + b'\nCONTROL MUTATION\n')
run('changed-payload', copy, 1)
target.write_bytes(saved)
target.unlink()
run('missing-payload', copy, 1)
target.write_bytes(saved)
extra = copy / '.extra-control'
extra.write_text('extra\n')
run('extra-hidden-payload', copy, 1)
extra.unlink()
wrong = anchor_args.copy()
wrong[1] = ('0' if a.final_sha256[0] != '0' else '1') + a.final_sha256[1:]
run('wrong-final-anchor', copy, 1, wrong)
report = copy / 'REPORT.md'
saved_report = report.read_bytes()
report.write_bytes(saved_report + b'\nCONTROL MUTATION\n')
run('changed-outside-report', copy, 1)
report.write_bytes(saved_report)
run('restored-copy', copy, 0)
run('original-after', r, 0)
(outside / 'results.json').write_text(json.dumps({'scope': 'artifact controls only; originals read-only', 'cases': rows}, indent=2) + '\n')
print(json.dumps({'control_cases': len(rows), 'all_expected_outcomes': True, 'receipt': str(outside / 'results.json')}))
