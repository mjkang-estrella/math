#!/usr/bin/env python3
"""Copied-tree integrity controls. Writes only review scratch; never author files."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).absolute().parent


def snapshot(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in root.rglob('*') if p.is_file() and not p.is_symlink()}


def link(root, hard=False):
    p = root / 'review.md'
    content = root / 'tmp/content'
    content.parent.mkdir()
    content.write_bytes(p.read_bytes())
    p.unlink()
    if hard:
        os.link(content, p)
    else:
        p.symlink_to(content)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--anchor', required=True)
    a = p.parse_args()
    cases = [
        ('positive', None, 'PASS'),
        ('wrong_anchor', None, 'external manifest anchor'),
        ('append', lambda r: (r/'review.md').write_bytes((r/'review.md').read_bytes()+b'\n'), 'payload size'),
        ('same_size', lambda r: (r/'review.md').write_bytes(b'!'+(r/'review.md').read_bytes()[1:]), 'payload hash'),
        ('missing', lambda r: (r/'review.md').unlink(), 'exact membership'),
        ('extra', lambda r: (r/'EXTRA').write_text('extra'), 'exact membership'),
        ('manifest', lambda r: (r/'MANIFEST.json').write_bytes((r/'MANIFEST.json').read_bytes()+b'\n'), 'external manifest anchor'),
        ('symlink', lambda r: link(r), 'regular single-link'),
        ('hardlink', lambda r: link(r, True), 'regular single-link'),
    ]
    (HERE/'tmp').mkdir(exist_ok=True)
    rows = []
    with tempfile.TemporaryDirectory(dir=HERE/'tmp', prefix='own-controls-') as td:
        for name, mutate, reason in cases:
            dst = Path(td) / name
            shutil.copytree(HERE, dst, ignore=shutil.ignore_patterns('tmp'))
            if mutate:
                mutate(dst)
            anchor = a.anchor if name != 'wrong_anchor' else ('1' if a.anchor[0] != '1' else '0')+a.anchor[1:]
            before = snapshot(dst)
            run = subprocess.run([sys.executable, '-I', '-B', str(dst/'verify.py'), '--anchor', anchor], text=True, capture_output=True)
            assert (run.returncode == 0) == (reason == 'PASS'), (name, run.stdout, run.stderr)
            assert reason in run.stdout+run.stderr, (name, reason, run.stdout, run.stderr)
            assert before == snapshot(dst), ('verifier wrote files', name)
            rows.append({'case': name, 'matched': True, 'read_only': True, 'exit_code': run.returncode})
    print(json.dumps({'scope': 'integrity failure-mode controls only', 'cases': rows}, indent=2))


if __name__ == '__main__':
    main()
