#!/usr/bin/env python3
"""Reason-checked positive and negative controls for the T212M manuscript review seal; MIT.
Adapted from ../t212m-manuscript-review-r1/controls.py (only the module docstring changed).
The original is authenticated before and after; every mutation runs on a disposable copy
under a new --output directory, which also receives the receipt."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import socket
import subprocess

ROOT = Path(__file__).absolute().parent
CASES = [
    ('positive', None),
    ('wrong-anchor', 'external anchor mismatch'),
    ('malformed-anchor', 'malformed anchor'),
    ('changed-review', 'file inventory mismatch'),
    ('changed-checks', 'file inventory mismatch'),
    ('missing-file', 'file inventory mismatch'),
    ('extra-file', 'file inventory mismatch'),
    ('extra-directory', 'directory inventory mismatch'),
    ('nested-manifest', 'file inventory mismatch'),
    ('payload-symlink', 'symlink entry'),
    ('extra-symlink', 'symlink entry'),
    ('payload-hardlink', 'hardlink entry'),
    ('fifo', 'nonregular entry'),
    ('socket', 'nonregular entry'),
    ('manifest-hardlink', 'unsafe manifest'),
    ('manifest-symlink', 'unsafe manifest'),
    ('root-link', 'symlink root ancestry'),
    ('self-reseal', 'external anchor mismatch'),
    ('verdict-edit-reanchored', 'manifest metadata mismatch'),
    ('inventory-forge-reanchored', 'file inventory mismatch'),
]


def run(root, anchor):
    return subprocess.run(['python3', '-B', str(ROOT / 'verify.py'), '--root', str(root), '--anchor', anchor],
                          text=True, capture_output=True)


def rewrite_manifest(dest, edit):
    path = dest / 'manifest.json'
    manifest = json.loads(path.read_text())
    edit(manifest)
    path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    original = run(ROOT, args.anchor)
    if original.returncode:
        raise SystemExit('original failed: ' + original.stderr)
    out = args.output.absolute()
    out.mkdir(parents=True, exist_ok=False)
    results = []
    for case, reason in CASES:
        dest = out / case
        shutil.copytree(ROOT, dest, symlinks=True)
        review = dest / 'review.md'
        anchor = args.anchor
        if case == 'wrong-anchor':
            anchor = 'f' * 64
        elif case == 'malformed-anchor':
            anchor = args.anchor[:63]
        elif case == 'changed-review':
            review.write_text(review.read_text().replace('REQUIRED: none.', 'REQUIRED: repairs.'))
        elif case == 'changed-checks':
            p = dest / 'checks.json'
            p.write_bytes(p.read_bytes() + b'\n')
        elif case == 'missing-file':
            (dest / 'reading-limits.md').unlink()
        elif case == 'extra-file':
            (dest / 'extra.txt').write_text('extra')
        elif case == 'extra-directory':
            (dest / 'extra').mkdir()
        elif case == 'nested-manifest':
            (dest / 'nested').mkdir()
            (dest / 'nested' / 'manifest.json').write_text('{}')
        elif case == 'payload-symlink':
            review.unlink()
            review.symlink_to('reading-limits.md')
        elif case == 'extra-symlink':
            (dest / 'link').symlink_to('review.md')
        elif case == 'payload-hardlink':
            os.link(review, out / (case + '-outside-link'))
        elif case == 'fifo':
            review.unlink()
            os.mkfifo(review)
        elif case == 'socket':
            review.unlink()
            s = socket.socket(socket.AF_UNIX)
            s.bind(str(review))
            s.close()
        elif case == 'manifest-hardlink':
            os.link(dest / 'manifest.json', out / (case + '-outside-link'))
        elif case == 'manifest-symlink':
            target = out / (case + '-outside-manifest.json')
            shutil.copyfile(dest / 'manifest.json', target)
            (dest / 'manifest.json').unlink()
            (dest / 'manifest.json').symlink_to(target)
        elif case == 'root-link':
            link = out / 'root-alias'
            link.symlink_to(dest, target_is_directory=True)
            dest = link
        elif case == 'self-reseal':
            review.write_text(review.read_text() + '\nchanged\n')
            data = review.read_bytes()
            rewrite_manifest(dest, lambda m: m['files'].update(
                {'review.md': {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}}))
        elif case == 'verdict-edit-reanchored':
            anchor = rewrite_manifest(dest, lambda m: m.update({'verdict': 'REPAIRS_REQUIRED'}))
        elif case == 'inventory-forge-reanchored':
            review.write_text(review.read_text().replace('REQUIRED: none.', 'REQUIRED: repairs.'))
            anchor = rewrite_manifest(dest, lambda m: m['files'].pop('checks.json'))
        result = run(dest, anchor)
        accepted = result.returncode == 0
        ok = accepted if reason is None else (not accepted and reason in result.stderr)
        results.append({'case': case, 'accepted': accepted, 'expected_reason': reason,
                        'passed': ok, 'stdout': result.stdout, 'stderr': result.stderr})
        if not ok:
            raise AssertionError((case, result.returncode, result.stdout, result.stderr))
    final = run(ROOT, args.anchor)
    if final.returncode:
        raise SystemExit('original failed after controls: ' + final.stderr)
    receipt = {'identity_only': True, 'anchor': args.anchor, 'controls': len(results),
               'all_expected': True, 'original_rechecked_after': True, 'results': results}
    raw = (json.dumps(receipt, indent=2) + '\n').encode()
    (out / 'receipt.json').write_bytes(raw)
    print(json.dumps({'controls': len(results), 'all_expected': True,
                      'receipt': str(out / 'receipt.json'),
                      'receipt_sha256': hashlib.sha256(raw).hexdigest()}))


if __name__ == '__main__':
    main()
