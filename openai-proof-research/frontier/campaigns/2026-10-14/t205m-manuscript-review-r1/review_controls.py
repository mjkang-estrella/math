#!/usr/bin/env python3
"""Positive, wrong-anchor and copied-mutation controls for the review seal; MIT.
The original is authenticated first; every mutation runs on a /var/tmp copy,
and each rejection must carry its expected reason."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).absolute().parent
REVIEW_MARK = 'Required repairs: none.'


def run(root, anchor):
    return subprocess.run(['python3', '-B', str(root / 'verify.py'), '--anchor', anchor],
                          text=True, capture_output=True)


def rewrite_manifest(dest, edit):
    path = dest / 'review-manifest.json'
    manifest = json.loads(path.read_text())
    edit(manifest)
    raw = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
    path.write_bytes(raw)
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    original = run(ROOT, args.anchor)
    if original.returncode:
        raise SystemExit('original failed: ' + original.stderr)
    if REVIEW_MARK not in (ROOT / 'review.md').read_text():
        raise SystemExit('review mark missing')
    expected = {
        'positive': 'PASS_IDENTITY_ONLY', 'wrong-anchor': 'external anchor mismatch',
        'malformed-anchor': 'bad anchor', 'changed-review': 'exact inventory mismatch',
        'changed-script': 'exact inventory mismatch', 'changed-output': 'exact inventory mismatch',
        'missing-log': 'exact inventory mismatch', 'extra-file': 'exact inventory mismatch',
        'extra-directory': 'exact inventory mismatch', 'nested-manifest': 'exact inventory mismatch',
        'payload-link': 'symlink', 'payload-hardlink': 'nonregular or hardlink',
        'fifo': 'nonregular or hardlink', 'manifest-hardlink': 'unsafe manifest',
        'root-link': 'symlink root or ancestor', 'self-reseal': 'external anchor mismatch',
        'verdict-edit': 'external anchor mismatch',
        'verdict-edit-new-anchor': 'manifest metadata mismatch',
        'count-claim-new-anchor': 'manifest metadata mismatch',
    }
    results = []
    with tempfile.TemporaryDirectory(prefix='t205m-msr1-controls-', dir='/var/tmp') as tmp:
        base = Path(tmp)
        for case, reason in expected.items():
            dest = base / case
            shutil.copytree(ROOT, dest)
            review = dest / 'review.md'
            anchor = args.anchor
            if case == 'wrong-anchor':
                anchor = 'f' * 64
            elif case == 'malformed-anchor':
                anchor = args.anchor[:63]
            elif case == 'changed-review':
                review.write_text(review.read_text().replace(REVIEW_MARK, 'Required repairs: see below.'))
            elif case == 'changed-script':
                p = dest / 'independent_finite.py'
                p.write_bytes(p.read_bytes() + b'\n')
            elif case == 'changed-output':
                p = dest / 'independent-finite-out.json'
                p.write_text(p.read_text().replace('PASS_REVIEWER_INDEPENDENT_FINITE', 'FAIL'))
            elif case == 'missing-log':
                (dest / 'logs/independent-finite.stderr').unlink()
            elif case == 'extra-file':
                (dest / 'extra.txt').write_text('extra')
            elif case == 'extra-directory':
                (dest / 'extra').mkdir()
            elif case == 'nested-manifest':
                (dest / 'logs/review-manifest.json').write_text('{}')
            elif case == 'payload-link':
                review.unlink()
                review.symlink_to('reading-limits.md')
            elif case == 'payload-hardlink':
                os.link(review, base / 'linked-review')
            elif case == 'fifo':
                review.unlink()
                os.mkfifo(review)
            elif case == 'manifest-hardlink':
                os.link(dest / 'review-manifest.json', base / 'linked-manifest')
            elif case == 'root-link':
                link = base / 'root-alias'
                link.symlink_to(dest, target_is_directory=True)
                dest = link
            elif case == 'self-reseal':
                review.write_text(review.read_text() + '\nchanged\n')
                data = review.read_bytes()
                rewrite_manifest(dest, lambda m: m['files'].__setitem__(
                    'review.md', {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}))
            elif case == 'verdict-edit':
                rewrite_manifest(dest, lambda m: m.__setitem__('verdict', 'REPAIRS_REQUIRED'))
            elif case == 'verdict-edit-new-anchor':
                anchor = rewrite_manifest(dest, lambda m: m.__setitem__('verdict', 'REPAIRS_REQUIRED'))
            elif case == 'count-claim-new-anchor':
                anchor = rewrite_manifest(dest, lambda m: m.__setitem__('campaign_count_change', True))
            result = run(dest, anchor)
            accepted = result.returncode == 0
            if accepted != (case == 'positive') or reason not in result.stdout + result.stderr:
                raise AssertionError((case, result.returncode, result.stdout, result.stderr))
            results.append({'case': case, 'accepted': accepted, 'reason': reason})
    print(json.dumps({'identity_only': True, 'anchor': args.anchor, 'results': results}, indent=2))


if __name__ == '__main__':
    main()
