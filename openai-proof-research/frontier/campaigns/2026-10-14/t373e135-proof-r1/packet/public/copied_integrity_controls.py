"""Run nine integrity controls on a disposable copy in the exclusive root.

Requires detached anchors as arguments. No original packet is mutated.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    a = ap.parse_args()
    root = Path(__file__).resolve().parents[2]
    assert root.name == 't373e135-proof-r1'
    work = root / 'controls' / 'review-copy'
    if work.exists():
        raise RuntimeError('refusing to reuse control copy')
    work.mkdir(parents=True)
    shutil.copytree(root / 'packet', work / 'packet')
    for name in ['FINAL.md', 'REPORT.md']:
        shutil.copy2(root / name, work / name)
    args = [sys.executable, '-B', str(root / 'packet/public/verify_packet.py'), str(work),
            '--manifest-sha', a.manifest_sha, '--final-sha', a.final_sha,
            '--report-sha', a.report_sha]
    rows = []

    def check(label, expected):
        r = subprocess.run(args, capture_output=True, text=True, timeout=30)
        rows.append({'case': label, 'expected_exit': expected, 'actual_exit': r.returncode,
                     'output': json.loads(r.stdout)})
        if r.returncode != expected:
            raise RuntimeError('unexpected copied-control outcome: ' + label)

    try:
        check('copied baseline', 0)
        for rel in ['packet/public/review.md', 'packet/MANIFEST.json', 'FINAL.md', 'REPORT.md']:
            p = work / rel
            original = p.read_bytes()
            p.chmod(0o644)
            p.write_bytes(original + b'\nCOPIED CONTROL ONLY\n')
            check('altered ' + rel, 1)
            p.write_bytes(original)
        p = work / 'packet/private/incoming/packet/public/FROZEN-SCOPE.md'
        original = p.read_bytes()
        p.unlink()
        check('missing immutable incoming scope copy', 1)
        p.write_bytes(original)
        p = work / 'packet/unlisted.txt'
        p.write_text('copied control only')
        check('unlisted regular file', 1)
        p.unlink()
        p = work / 'packet/symlink-control'
        p.symlink_to('public/review.md')
        check('symlink file', 1)
        p.unlink()
        check('restored copied baseline', 0)
        result = {'controls': rows, 'all_expected_outcomes': True,
                  'limits': 'Copied byte-integrity controls only, no mathematical or original-preservation inference.'}
        (root / 'copied-integrity-controls.json').write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps({'cases': len(rows), 'negative_cases': 7, 'all_expected_outcomes': True}))
    finally:
        shutil.rmtree(work)


if __name__ == '__main__':
    main()
