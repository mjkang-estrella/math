#!/usr/bin/env python3
"""Run byte-integrity controls on a disposable copy inside the assigned root."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('root', type=Path)
    p.add_argument('--final-sha', required=True)
    p.add_argument('--manifest-sha', required=True)
    p.add_argument('--report-sha', required=True)
    a = p.parse_args()
    root = a.root.resolve()
    if root.name != 't373e135-contribution-r1':
        raise ValueError('wrong assigned root')
    work = root / 'disposable-review-controls'
    if work.exists():
        raise ValueError('refusing existing work directory')
    work.mkdir()
    rows = []
    try:
        shutil.copytree(root / 'packet', work / 'packet')
        for name in ['FINAL.md', 'REPORT.md']:
            shutil.copy2(root / name, work / name)
        args = [sys.executable, str(root / 'packet/public/verify_packet.py'), str(work),
                '--final-sha', a.final_sha, '--manifest-sha', a.manifest_sha,
                '--report-sha', a.report_sha]

        def run(name, expected):
            proc = subprocess.run(args, capture_output=True, text=True)
            rows.append({'case': name, 'expected_exit': expected,
                         'actual_exit': proc.returncode, 'output': proc.stdout,
                         'stderr': proc.stderr})
            if proc.returncode != expected:
                raise ValueError('unexpected control result: ' + name)

        run('unchanged copy', 0)
        target = work / 'packet/public/review.md'
        old = target.read_bytes()
        target.write_bytes(old + b'\nCONTROL\n')
        run('modified review', 1)
        target.unlink()
        run('missing review', 1)
        target.write_bytes(old)
        extra = work / 'packet/extra-control'
        extra.write_text('control')
        run('extra file', 1)
        extra.unlink()
        extra.symlink_to('public/review.md')
        run('symlink', 1)
        extra.unlink()
        for name in ['FINAL.md', 'REPORT.md', 'packet/MANIFEST.json']:
            target = work / name
            old = target.read_bytes()
            target.write_bytes(old + b'\n')
            run('altered detached ' + name, 1)
            target.write_bytes(old)
        run('restored copy', 0)
        result = {'cases': rows, 'all_expected_outcomes_observed': True,
                  'limits': 'Artifact controls only. Original packet not mutated.'}
        (root / 'copied-controls.json').write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps({'cases': len(rows), 'negative_cases': 7}))
    finally:
        shutil.rmtree(work)


if __name__ == '__main__':
    main()
