#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Mutation controls for verify.py. Every case runs on a fresh copy under a
new temporary directory; the original directory is only read.
Usage: controls.py ANCHOR"""
import json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

SRC = Path(os.path.abspath(__file__)).parent


def run(root, anchor):
    p = subprocess.run([sys.executable, '-B', str(root / 'verify.py'), anchor],
                       capture_output=True, text=True)
    return {'returncode': p.returncode, 'output': (p.stdout + p.stderr).strip()}


def main(anchor):
    base = Path(tempfile.mkdtemp(prefix='t027o-review-controls-', dir='/var/tmp'))
    n = [0]

    def fresh():
        n[0] += 1
        d = base / f'case{n[0]}' / 'r'
        shutil.copytree(SRC, d, symlinks=True)
        return d

    cases = {}
    cases['unchanged_copy'] = run(fresh(), anchor)
    d = fresh(); (d / 'review.md').write_bytes((d / 'review.md').read_bytes() + b' ')
    cases['payload'] = run(d, anchor)
    d = fresh(); (d / 'reading-limits.md').unlink()
    cases['missing'] = run(d, anchor)
    d = fresh(); (d / 'extra.txt').write_text('x')
    cases['extra_file'] = run(d, anchor)
    d = fresh(); (d / 'emptydir').mkdir()
    cases['extra_empty_directory'] = run(d, anchor)
    d = fresh(); p = d / 'private/primary/litt-survey.txt'; p.write_bytes(p.read_bytes()[:-1])
    cases['private_payload'] = run(d, anchor)
    d = fresh(); link = d.parent / 'link'; link.symlink_to(d)
    cases['root_symlink'] = run(link, anchor)
    d = fresh(); real = d.parent.parent / 'real'; d.parent.rename(real)
    (d.parent.parent / 'ancestor').symlink_to(real)
    cases['ancestor_symlink'] = run(d.parent.parent / 'ancestor' / 'r', anchor)
    d = fresh(); os.link(d / 'review.md', d.parent / 'hl')
    cases['hardlink'] = run(d, anchor)
    d = fresh(); os.mkfifo(d / 'pipe')
    cases['fifo'] = run(d, anchor)
    d = fresh(); (d / 'private' / 'manifest.json').write_text('{}')
    cases['nested_manifest'] = run(d, anchor)
    d = fresh(); (d / 'review.md').unlink(); (d / 'review.md').symlink_to(d / 'checkpoint.md')
    cases['file_symlink'] = run(d, anchor)
    d = fresh()
    m = json.loads((d / 'manifest.json').read_text())
    (d / 'review.md').write_text('resealed\n')
    import hashlib
    b = (d / 'review.md').read_bytes()
    m['files']['review.md'] = {'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}
    (d / 'manifest.json').write_text(json.dumps(m, indent=1, sort_keys=True) + '\n')
    cases['self_reseal'] = run(d, anchor)
    cases['wrong_anchor'] = run(fresh(), '0' * 64)
    cases['short_anchor'] = run(fresh(), anchor[:63])
    ok = cases['unchanged_copy']['returncode'] == 0 and all(
        v['returncode'] == 1 for k, v in cases.items() if k != 'unchanged_copy')
    print(json.dumps({'status': 'PASS' if ok else 'FAIL', 'workdir': str(base), 'cases': cases}, indent=1))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1]))
