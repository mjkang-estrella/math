#!/usr/bin/env python3
"""Copied positive and reason-checked negative controls (T298P contribution r2).

Never modifies the repository. Each case copies files into a fresh directory
under /var/tmp (tempfile.mkdtemp), mutates only that copy, runs the verifier
from the copy with python3 -I, and checks both the return code and the exact
failure reason prefix.

  --mode author : controls for the author verifier fresh-structural-discovery-r104/verify.py
                  (public files copied; --private-root points at the real private
                  directory, which is read only).
  --mode self   : controls for this review's verify.py, after sealing (needs --anchor).
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

AUTHOR_ANCHOR = 'b6c525288bd6a7203d13c8b8ed4b696e14a0f8c3a06cd30cb6fbe871d6dfbeb3'
AUTHOR_REL = 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r104'


def run(verifier, args):
    p = subprocess.run([sys.executable, '-I', str(verifier)] + args, cwd='/var/tmp',
                       capture_output=True, text=True)
    out = (p.stdout + p.stderr).strip()
    return p.returncode, out


def copy_public(src, dst):
    dst.mkdir()
    for f in src.iterdir():
        if f.name == 'private':
            continue
        shutil.copy2(f, dst / f.name)


def append_byte(path):
    with open(path, 'ab') as fh:
        fh.write(b'\n')


def author_cases(repo):
    src = repo / AUTHOR_REL
    private = str(src / 'private')
    cases = [
        ('positive copy', None, AUTHOR_ANCHOR, 0, '{"status": "PASS"'),
        ('wrong external anchor', None, '0' * 64, 1, 'FAIL: external manifest anchor'),
        ('candidate.md one-byte append', lambda d: append_byte(d / 'candidate.md'), AUTHOR_ANCHOR, 1,
         'FAIL: payload candidate.md'),
        ('extra public file', lambda d: (d / 'extra.md').write_text('x'), AUTHOR_ANCHOR, 1,
         'FAIL: exact public membership'),
        ('missing comparison.md', lambda d: (d / 'comparison.md').unlink(), AUTHOR_ANCHOR, 1,
         'FAIL: exact public membership'),
        ('unconditional-score-construction.md one-byte append',
         lambda d: append_byte(d / 'unconditional-score-construction.md'), AUTHOR_ANCHOR, 1,
         'FAIL: payload unconditional-score-construction.md'),
    ]
    results = []
    for name, mutate, anchor, rc_exp, reason in cases:
        root = Path(tempfile.mkdtemp(prefix='t298p-c2-authorctl-', dir='/var/tmp'))
        d = root / 'pkt'
        copy_public(src, d)
        if mutate:
            mutate(d)
        rc, out = run(d / 'verify.py', ['--anchor', anchor, '--repo', str(repo), '--private-root', private])
        results.append({'case': name, 'workdir': str(d), 'rc': rc, 'output': out,
                        'expected_rc': rc_exp, 'expected_reason_prefix': reason,
                        'ok': rc == rc_exp and out.startswith(reason)})
    return results


def self_cases(repo, here, anchor):
    def symlink(d):
        os.symlink('review.md', d / 'link.md')

    def hardlink(d):
        os.link(d / 'review.md', d / 'review-hardlink.md')

    def subdir(d):
        (d / 'sub').mkdir()

    cases = [
        ('positive copy', None, anchor, 0, '{"author_anchors"'),
        ('wrong external anchor', None, 'f' * 64, 1, 'FAIL: external manifest anchor'),
        ('review.md one-byte append', lambda d: append_byte(d / 'review.md'), anchor, 1,
         'FAIL: payload review.md'),
        ('extra file', lambda d: (d / 'extra.md').write_text('x'), anchor, 1, 'FAIL: exact membership'),
        ('missing reading-limits.md', lambda d: (d / 'reading-limits.md').unlink(), anchor, 1,
         'FAIL: exact membership'),
        ('symlink entry', symlink, anchor, 1, 'FAIL: symlink link.md'),
        ('hard link entry', hardlink, anchor, 1, 'FAIL: link count'),
        ('subdirectory entry', subdir, anchor, 1, 'FAIL: non-regular entry sub'),
    ]
    results = []
    for name, mutate, anc, rc_exp, reason in cases:
        root = Path(tempfile.mkdtemp(prefix='t298p-c2-selfctl-', dir='/var/tmp'))
        d = root / 'r2'
        d.mkdir()
        for f in here.iterdir():
            shutil.copy2(f, d / f.name)
        if mutate:
            mutate(d)
        rc, out = run(d / 'verify.py', ['--anchor', anc, '--repo', str(repo)])
        results.append({'case': name, 'workdir': str(d), 'rc': rc, 'output': out,
                        'expected_rc': rc_exp, 'expected_reason_prefix': reason,
                        'ok': rc == rc_exp and out.startswith(reason)})
    return results


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--mode', choices=['author', 'self'], required=True)
    p.add_argument('--repo', required=True)
    p.add_argument('--anchor')
    a = p.parse_args()
    repo = Path(a.repo).resolve()
    here = Path(__file__).resolve().parent
    if a.mode == 'author':
        res = author_cases(repo)
        helper = repo / AUTHOR_REL / 'verify.py'
    else:
        if not a.anchor:
            raise SystemExit('--anchor required for --mode self')
        res = self_cases(repo, here, a.anchor)
        helper = here / 'verify.py'
    print(json.dumps({'mode': a.mode,
                      'helper_sha256': hashlib.sha256(helper.read_bytes()).hexdigest(),
                      'cases': res, 'all_ok': all(r['ok'] for r in res)}, indent=1))


if __name__ == '__main__':
    main()
