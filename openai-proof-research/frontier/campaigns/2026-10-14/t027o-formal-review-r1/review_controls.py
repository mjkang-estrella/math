#!/usr/bin/env python3
"""Copied mutation controls for this review packet (MIT). Writes only a /var/tmp temp dir."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).absolute().parent

def run(root, anchor):
    r = subprocess.run(['python3', '-B', str(root / 'verify.py'), '--anchor', anchor],
                       capture_output=True, text=True, timeout=60)
    return r.returncode, (r.stdout + r.stderr).strip()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    anchor = ap.parse_args().anchor
    code, text = run(ROOT, anchor)
    if code:
        raise SystemExit('original packet rejected: ' + text)
    def edit(p, old, new):
        data = p.read_bytes()
        assert data.count(old) == 1, (p, old)
        p.write_bytes(data.replace(old, new))
    def reseal(d):
        edit(d / 'review.md', b'There are no required objections.', b'There are required objections.')
        m = json.loads((d / 'review-manifest.json').read_text())
        data = (d / 'review.md').read_bytes()
        m['files']['review.md'] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
        (d / 'review-manifest.json').write_text(json.dumps(m))
    cases = {
        'positive': (lambda d, b: None, 'PASS_REVIEW_IDENTITY_ONLY'),
        'wrong-anchor': (lambda d, b: None, 'external anchor mismatch'),
        'verdict-edit': (lambda d, b: edit(d / 'review.md', b'Verdict: **PASS_SCOPED_FORMAL_SUPPORT**', b'Verdict: **FAIL**'), 'exact inventory mismatch'),
        'lean-edit': (lambda d, b: edit(d / 'src/T027OReview.lean', b'theorem drop_hdiag', b'theorem drop_hdiag2'), 'exact inventory mismatch'),
        'log-edit': (lambda d, b: (d / 'results/independent-build/types-axioms.log').write_text('x'), 'exact inventory mismatch'),
        'missing-file': (lambda d, b: (d / 'results/input-controls.json').unlink(), 'exact inventory mismatch'),
        'extra-file': (lambda d, b: (d / 'results/extra.txt').write_text(''), 'exact inventory mismatch'),
        'extra-directory': (lambda d, b: (d / 'results/extra').mkdir(), 'exact inventory mismatch'),
        'payload-symlink': (lambda d, b: ((d / 'review.md').unlink(), (d / 'review.md').symlink_to('verify.py')), 'symlink review.md'),
        'payload-hardlink': (lambda d, b: os.link(d / 'review.md', b / 'hl-review'), 'nonregular or hardlink review.md'),
        'fifo': (lambda d, b: ((d / 'review.md').unlink(), os.mkfifo(d / 'review.md')), 'nonregular or hardlink review.md'),
        'manifest-hardlink': (lambda d, b: os.link(d / 'review-manifest.json', b / 'hl-manifest'), 'unsafe manifest'),
        'nested-manifest': (lambda d, b: (d / 'results/review-manifest.json').write_text('{}'), 'exact inventory mismatch'),
        'self-reseal': (lambda d, b: reseal(d), 'external anchor mismatch'),
    }
    results = []
    with tempfile.TemporaryDirectory(prefix='t027o-review-seal-controls-', dir='/var/tmp') as tmp:
        base = Path(tmp)
        for name, (mutate, expect) in cases.items():
            d = base / name
            shutil.copytree(ROOT, d, symlinks=True)
            sub = base / ('aux-' + name)
            sub.mkdir()
            mutate(d, sub)
            code, text = run(d, '0' * 64 if name == 'wrong-anchor' else anchor)
            accepted = code == 0
            if accepted != (name == 'positive') or expect not in text:
                raise AssertionError((name, code, text))
            results.append({'case': name, 'accepted': accepted, 'reason': text})
    print(json.dumps({'identity_only': True, 'results': results}, indent=2))

if __name__ == '__main__':
    main()
