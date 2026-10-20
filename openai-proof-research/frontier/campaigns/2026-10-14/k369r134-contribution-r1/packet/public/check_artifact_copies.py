#!/usr/bin/env python3
"""Bounded mutation controls on copies inside the exclusive review root.

Run only after sealing, passing the detached anchors from the handoff.
Uses the trusted original verifier to inspect each copied root.
Writes only the outside receipt and temporary material under work/.
"""
import argparse
import datetime
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    result = {}
    def excluded(n):
        n = n.lower()
        return (n.startswith('t205q140-') or n.startswith('k369r134-proof-')
                or fnmatch.fnmatchcase(n, '*arithmetic*r104*')
                or fnmatch.fnmatchcase(n, '*structural*r141*'))
    for base, dirs, files in os.walk(root / 'packet', followlinks=False):
        if any(excluded(n) for n in dirs + files):
            raise AssertionError('excluded component in own packet')
        for n in dirs:
            if (Path(base) / n).is_symlink():
                raise AssertionError('symlink directory in baseline')
        for n in files:
            p = Path(base) / n
            if p.is_symlink():
                raise AssertionError('symlink payload in baseline')
            result[str(p.relative_to(root))] = sha(p)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    for n in ('final', 'manifest', 'report'):
        ap.add_argument('--' + n + '-sha256', required=True)
    a = ap.parse_args()
    root = a.root.resolve()
    anchor_args = ['--final-sha256', a.final_sha256,
                   '--manifest-sha256', a.manifest_sha256,
                   '--report-sha256', a.report_sha256]
    verifier = root / 'verify.py'
    before = snapshot(root)
    outcomes = []

    def test(name, target, expected, reason=None):
        p = subprocess.run([sys.executable, '-B', str(verifier), '--root', str(target), *anchor_args],
                           capture_output=True, text=True, timeout=30)
        ok = (p.returncode == 0) == expected
        if reason is not None:
            ok = ok and reason in p.stderr
        outcomes.append({'case': name, 'expected_pass': expected,
                         'control_pass': ok, 'returncode': p.returncode,
                         'stdout': p.stdout.strip(), 'stderr': p.stderr.strip()})
        if not ok:
            raise AssertionError(name)

    work = root / 'work'
    work.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='review-control-copy-', dir=work) as temp:
        copied = Path(temp)
        shutil.copytree(root / 'packet', copied / 'packet')
        for n in ('FINAL.json', 'MANIFEST.json', 'REPORT.md', 'verify.py'):
            shutil.copy2(root / n, copied / n)
        test('sealed_baseline', root, True)
        test('copied_baseline', copied, True)
        p = copied / 'packet/public/review.md'
        b = p.read_bytes()
        p.write_bytes(b + b'\nmutation\n')
        test('review_payload_mutation', copied, False, 'payload size mismatch')
        p.write_bytes(b)
        p = copied / 'packet/extra.txt'
        p.write_text('extra')
        test('unexpected_file', copied, False, 'exact packet file set mismatch')
        p.unlink()
        p = copied / 'REPORT.md'
        b = p.read_bytes()
        p.write_bytes(b + b'\nmutation\n')
        test('outside_report_mutation', copied, False, 'detached hash mismatch REPORT.md')
        p.write_bytes(b)
        p = copied / 'packet/public/review.md'
        b = p.read_bytes()
        p.unlink()
        p.symlink_to('technical-reduction.md')
        test('payload_symlink', copied, False, 'nonregular payload')
        p.unlink()
        p.write_bytes(b)
        p = copied / 'verify.py'
        b = p.read_bytes()
        p.write_bytes(b + b'\n# mutation\n')
        test('verifier_identity', copied, False, 'verifier identity mismatch')
        p.write_bytes(b)
        p = copied / 'MANIFEST.json'
        b = p.read_bytes()
        p.write_bytes(b + b' ')
        test('manifest_cannot_replace_detached_anchor', copied, False, 'detached hash mismatch MANIFEST.json')
        p.write_bytes(b)
        test('restored_copy', copied, True)
    after = snapshot(root)
    if before != after:
        raise AssertionError('sealed packet changed during controls')
    receipt = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'status': 'PASS_ARTIFACT_CONTROLS_ONLY', 'checks': outcomes,
               'sealed_packet_unchanged': True, 'temporary_copy_removed': True,
               'limits': 'Regular-file byte identities and expected rejection reasons only; no mathematical gate, empty-directory/mode/hardlink check or syscall write-denial claim.'}
    (root / 'INTEGRITY-CONTROLS.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'cases': len(outcomes), 'all_expected': True, 'sealed_packet_unchanged': True}))


if __name__ == '__main__':
    main()
