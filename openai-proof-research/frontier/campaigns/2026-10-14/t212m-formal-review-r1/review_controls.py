#!/usr/bin/env python3
"""Positive, wrong-anchor and copied-mutation controls for the T212M review seal; MIT.
Adapted from ../t205m-formal-review-r1/review_controls.py. The original is
authenticated first; every mutation runs on a /var/tmp copy."""
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
    return subprocess.run(['python3', '-B', str(root / 'verify.py'), '--anchor', anchor],
                          text=True, capture_output=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    original = run(ROOT, args.anchor)
    if original.returncode:
        raise SystemExit('original failed: ' + original.stderr)
    expected = {
        'positive': 'PASS_IDENTITY_ONLY', 'wrong-anchor': 'external anchor mismatch',
        'malformed-anchor': 'bad anchor', 'changed-review': 'exact inventory mismatch',
        'changed-lean': 'exact inventory mismatch', 'missing-log': 'exact inventory mismatch',
        'extra-file': 'exact inventory mismatch', 'extra-directory': 'exact inventory mismatch',
        'nested-manifest': 'exact inventory mismatch', 'payload-link': 'symlink',
        'payload-hardlink': 'nonregular or hardlink', 'fifo': 'nonregular or hardlink',
        'manifest-hardlink': 'unsafe manifest', 'root-link': 'symlink root or ancestor',
        'self-reseal': 'external anchor mismatch', 'verdict-edit': 'external anchor mismatch',
    }
    results = []
    with tempfile.TemporaryDirectory(prefix='t212m-review-controls-', dir='/var/tmp') as tmp:
        base = Path(tmp)
        for case, reason in expected.items():
            dest = base / case
            shutil.copytree(ROOT, dest)
            review = dest / 'review.md'
            anchor = args.anchor
            if case == 'wrong-anchor': anchor = 'f' * 64
            elif case == 'malformed-anchor': anchor = args.anchor[:63]
            elif case == 'changed-review':
                review.write_text(review.read_text().replace('REQUIRED: none.', 'REQUIRED: repairs.'))
            elif case == 'changed-lean':
                p = dest / 'Independent.lean'; p.write_bytes(p.read_bytes() + b'\n')
            elif case == 'missing-log': (dest / 'independent-logs/Independent.lean.log').unlink()
            elif case == 'extra-file': (dest / 'extra.txt').write_text('extra')
            elif case == 'extra-directory': (dest / 'extra').mkdir()
            elif case == 'nested-manifest': (dest / 'builder-run/review-manifest.json').write_text('{}')
            elif case == 'payload-link': review.unlink(); review.symlink_to('reading-limits.md')
            elif case == 'payload-hardlink': os.link(review, base / 'linked-review')
            elif case == 'fifo': review.unlink(); os.mkfifo(review)
            elif case == 'manifest-hardlink': os.link(dest / 'review-manifest.json', base / 'linked-manifest')
            elif case == 'root-link':
                link = base / 'root-alias'; link.symlink_to(dest, target_is_directory=True); dest = link
            elif case in ('self-reseal', 'verdict-edit'):
                manifest = json.loads((dest / 'review-manifest.json').read_text())
                if case == 'self-reseal':
                    review.write_text(review.read_text() + '\nchanged\n')
                    data = review.read_bytes()
                    manifest['files']['review.md'] = {'bytes': len(data),
                                                      'sha256': hashlib.sha256(data).hexdigest()}
                else:
                    manifest['verdict'] = 'REPAIRS_REQUIRED'
                (dest / 'review-manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
            result = run(dest, anchor)
            accepted = result.returncode == 0
            if accepted != (case == 'positive') or reason not in result.stdout + result.stderr:
                raise AssertionError((case, result.returncode, result.stdout, result.stderr))
            results.append({'case': case, 'accepted': accepted, 'reason': reason})
    print(json.dumps({'identity_only': True, 'anchor': args.anchor, 'results': results}, indent=2))


if __name__ == '__main__':
    main()
