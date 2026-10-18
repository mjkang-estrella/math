#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Positive, wrong-anchor and mutation controls for verify.py. Every case runs
on a fresh copy in a new temporary directory under --scratch; this directory
is only read. A case passes only if both exit code and reason match.
Usage: controls.py --anchor SHA256 --scratch DIR"""
import hashlib, json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

SRC = Path(os.path.abspath(__file__)).parent


def run(script, anchor_args):
    p = subprocess.run([sys.executable, '-B', str(script), *anchor_args],
                       capture_output=True, text=True)
    return p.returncode, p.stdout, p.stderr


def main(argv):
    if len(argv) != 5 or argv[1] != '--anchor' or argv[3] != '--scratch':
        print('usage: controls.py --anchor SHA256 --scratch DIR', file=sys.stderr)
        return 2
    anchor, scratch = argv[2], argv[4]
    base = Path(tempfile.mkdtemp(prefix='t027o-msr1-controls-', dir=scratch))
    n = [0]

    def fresh():
        n[0] += 1
        d = base / f'case{n[0]:02d}' / 'r'
        shutil.copytree(SRC, d, symlinks=True)
        return d

    cases = []

    def case(name, d, expect, args=None, script=None):
        if args is None:
            args = ['--anchor', anchor]
        rc, out, err = run(script or d / 'verify.py', args)
        if expect is None:
            ok = rc == 0 and '"PASS_REVIEW_IDENTITY_ONLY"' in out and err == ''
        else:
            ok = rc == 1 and err.startswith('INTEGRITY_REJECT: ' + expect)
        cases.append({'case': name, 'expected_reason': expect, 'exit_code': rc, 'pass': ok})

    try:
        case('positive', fresh(), None)
        case('wrong-anchor', fresh(), 'external manifest anchor mismatch',
             ['--anchor', '0' * 64])
        case('short-anchor', fresh(), 'external SHA256 anchor required',
             ['--anchor', anchor[:63]])
        case('missing-anchor', fresh(), 'external SHA256 anchor required', [])
        d = fresh(); p = d / 'review.md'; p.write_bytes(p.read_bytes() + b' ')
        case('payload-byte', d, 'exact inventory mismatch')
        d = fresh(); (d / 'reading-limits.md').unlink()
        case('missing-file', d, 'exact inventory mismatch')
        d = fresh(); (d / 'extra.txt').write_text('x')
        case('extra-file', d, 'exact inventory mismatch')
        d = fresh(); (d / 'emptydir').mkdir()
        case('extra-directory', d, 'exact inventory mismatch')
        d = fresh(); link = d.parent / 'link'; link.symlink_to(d)
        case('root-link', d, 'symlink ancestry', script=link / 'verify.py')
        d = fresh(); real = d.parent.parent / 'real'; d.parent.rename(real)
        (d.parent.parent / 'anc').symlink_to(real)
        case('ancestor-link', d, 'symlink ancestry',
             script=d.parent.parent / 'anc' / 'r' / 'verify.py')
        d = fresh(); (d / 'review.md').unlink(); (d / 'review.md').symlink_to(d / 'reading-limits.md')
        case('payload-link', d, 'symlink payload')
        d = fresh(); os.link(d / 'review.md', d.parent / 'hl')
        case('hardlink', d, 'hardlink')
        d = fresh(); os.mkfifo(d / 'pipe')
        case('fifo', d, 'nonregular entry')
        d = fresh(); (d / 'sub').mkdir(); (d / 'sub' / 'manifest.json').write_text('{}')
        case('nested-manifest', d, 'nested manifest')
        d = fresh()
        m = json.loads((d / 'manifest.json').read_text())
        (d / 'review.md').write_text('Verdict: resealed\n')
        b = (d / 'review.md').read_bytes()
        m['files']['review.md'] = {'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}
        (d / 'manifest.json').write_text(json.dumps(m, indent=1, sort_keys=True) + '\n')
        case('self-reseal', d, 'external manifest anchor mismatch')
    finally:
        shutil.rmtree(base)
    ok = all(c['pass'] for c in cases)
    print(json.dumps({'result': 'PASS_REVIEW_CONTROLS' if ok else 'FAIL_REVIEW_CONTROLS',
                      'scratch_removed': not base.exists(), 'cases': cases}, indent=1))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
