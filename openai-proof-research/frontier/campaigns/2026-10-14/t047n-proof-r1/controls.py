#!/usr/bin/env python3
"""Copied mutation controls for this review packet's verifier. MIT.
All mutations act on disposable copies under /var/tmp; the packet is untouched.

Usage: python3 -I controls.py --expected-manifest SHA256 --expected-verifier SHA256
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest', required=True)
    ap.add_argument('--expected-verifier', required=True)
    a = ap.parse_args()
    root = Path(os.path.abspath(__file__)).parent
    names = ['positive', 'wrong_manifest', 'wrong_verifier', 'edit_review', 'delete_review', 'extra_file',
             'extra_empty_dir', 'nested_manifest', 'root_symlink', 'ancestor_symlink', 'payload_symlink',
             'hardlink', 'fifo', 'edit_manifest', 'edit_verifier', 'self_reseal']
    results = {}
    with tempfile.TemporaryDirectory(prefix='t047n-r1-controls-', dir='/var/tmp') as td:
        td = Path(td)
        for name in names:
            c = td / name / 'packet'
            shutil.copytree(root, c)
            invoke = c
            mh, vh = a.expected_manifest, a.expected_verifier
            if name == 'wrong_manifest':
                mh = '0' * 64
            if name == 'wrong_verifier':
                vh = '0' * 64
            if name == 'edit_review':
                p = c / 'review.md'
                p.write_text(p.read_text().replace('PASS_FULL_T047N', 'FAIL', 1))
            if name == 'delete_review':
                (c / 'review.md').unlink()
            if name == 'extra_file':
                (c / 'extra.txt').write_text('extra')
            if name == 'extra_empty_dir':
                (c / 'empty').mkdir()
            if name == 'nested_manifest':
                (c / 'nested').mkdir()
                (c / 'nested' / 'manifest.json').write_text('{}')
            if name == 'root_symlink':
                invoke = td / name / 'root-link'
                invoke.symlink_to(c, target_is_directory=True)
            if name == 'ancestor_symlink':
                holder = td / name / 'holder'
                holder.mkdir()
                shutil.move(str(c), str(holder / 'packet'))
                link = td / name / 'holder-link'
                link.symlink_to(holder, target_is_directory=True)
                invoke = link / 'packet'
            if name == 'payload_symlink':
                p = c / 'review.md'
                body = p.read_bytes()
                outside = td / name / 'outside-review.md'
                outside.write_bytes(body)
                p.unlink()
                p.symlink_to(outside)
            if name == 'hardlink':
                os.link(c / 'review.md', c / 'review-hardlink.md')
            if name == 'fifo':
                os.mkfifo(c / 'fifo')
            if name == 'edit_manifest':
                with (c / 'manifest.json').open('a') as f:
                    f.write(' ')
            if name == 'edit_verifier':
                with (c / 'verify.py').open('a') as f:
                    f.write('\n# mutation\n')
            if name == 'self_reseal':
                p = c / 'review.md'
                p.write_text(p.read_text() + '\nmutation\n')
                m = json.loads((c / 'manifest.json').read_text())
                m['files']['review.md'] = {'bytes': p.stat().st_size, 'sha256': sha(p)}
                (c / 'manifest.json').write_text(json.dumps(m, sort_keys=True, indent=2) + '\n')
            cmd = [sys.executable, '-I', str(invoke / 'verify.py'), '--expected-manifest', mh,
                   '--expected-verifier', vh]
            p = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            ok = (p.returncode == 0) if name == 'positive' else (p.returncode != 0)
            if not ok:
                raise SystemExit('CONTROL FAILED ' + name + ': ' + p.stdout + p.stderr)
            results[name] = (p.stdout + p.stderr).strip()[:100]
    print(json.dumps({'status': 'PASS_ALL_COPIED_CONTROLS', 'cases': results}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
