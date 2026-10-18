#!/usr/bin/env python3
"""Copied mutation controls for the review seal; /var/tmp copies only (MIT)."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).absolute().parent
CASES = {
    'positive': 'PASS_REVIEW_IDENTITY_ONLY',
    'wrong-anchor': 'external anchor mismatch',
    'packet-anchor-as-review-anchor': 'external anchor mismatch',
    'malformed-anchor': 'bad anchor',
    'changed-review': 'exact membership mismatch',
    'changed-lean': 'exact membership mismatch',
    'missing-file': 'exact membership mismatch',
    'extra-file': 'exact membership mismatch',
    'extra-directory': 'exact membership mismatch',
    'nested-manifest': 'exact membership mismatch',
    'root-link': 'symlink root or ancestor',
    'payload-link': 'symlink',
    'payload-hardlink': 'nonregular or hardlink',
    'manifest-hardlink': 'unsafe manifest',
    'self-reseal': 'external anchor mismatch',
}


def run(root, anchor):
    return subprocess.run(['python3', '-B', str(root / 'verify.py'), '--anchor', anchor],
                          capture_output=True, text=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    first = run(ROOT, args.anchor)
    if first.returncode:
        raise SystemExit('original does not verify: ' + first.stderr)
    results = []
    with tempfile.TemporaryDirectory(prefix='t117q-review-seal-controls-', dir='/var/tmp') as tmp:
        base = Path(tmp)
        for case, reason in CASES.items():
            dest = base / case
            shutil.copytree(ROOT, dest, symlinks=True)
            anchor = args.anchor
            review = dest / 'review.md'
            if case == 'wrong-anchor':
                anchor = '0' * 64
            elif case == 'packet-anchor-as-review-anchor':
                anchor = 'b741e2d76e9383238b5f3e975c634e2bb48b75eaa00dc1fb93371b0a1c139b37'
            elif case == 'malformed-anchor':
                anchor = 'xyz'
            elif case == 'changed-review':
                review.write_text(review.read_text().replace('PASS_SCOPED_T117Q', 'FAIL_T117Q', 1))
            elif case == 'changed-lean':
                p = dest / 'Independent.lean'
                p.write_bytes(p.read_bytes() + b'\n-- changed\n')
            elif case == 'missing-file':
                (dest / 'declaration-audit.json').unlink()
            elif case == 'extra-file':
                (dest / 'extra.txt').write_text('extra')
            elif case == 'extra-directory':
                (dest / 'extra').mkdir()
            elif case == 'nested-manifest':
                (dest / 'logs' / 'review-manifest.json').write_text('{}')
            elif case == 'root-link':
                link = base / 'root-alias'
                link.symlink_to(dest, target_is_directory=True)
                dest = link
            elif case == 'payload-link':
                review.unlink()
                review.symlink_to('declaration-audit.json')
            elif case == 'payload-hardlink':
                os.link(review, base / 'linked-review')
            elif case == 'manifest-hardlink':
                os.link(dest / 'review-manifest.json', base / 'linked-manifest')
            elif case == 'self-reseal':
                review.write_text(review.read_text().replace('PASS_SCOPED_T117Q', 'FAIL_T117Q', 1))
                manifest = json.loads((dest / 'review-manifest.json').read_text())
                data = review.read_bytes()
                manifest['files']['review.md'] = {'bytes': len(data),
                                                  'sha256': hashlib.sha256(data).hexdigest()}
                (dest / 'review-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
            result = run(dest, anchor)
            accepted = result.returncode == 0
            if accepted != (case == 'positive') or reason not in result.stdout + result.stderr:
                raise AssertionError((case, result.returncode, result.stdout, result.stderr))
            results.append({'case': case, 'accepted': accepted, 'reason': reason})
    print(json.dumps({'identity_only': True, 'anchor': args.anchor, 'results': results}, indent=2))


if __name__ == '__main__':
    main()
