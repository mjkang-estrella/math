#!/usr/bin/env python3
"""R4 review verifier controls adapted from author controls.py. MIT, Myeongjin Kang."""
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

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--anchor', required=True)
    a = p.parse_args()
    cases = [
        ('positive', None, 'PASS'),
        ('wrong_anchor', None, 'external manifest anchor'),
        ('append_payload', lambda r: (r / 'review.md').write_bytes((r / 'review.md').read_bytes() + b'\n'), 'payload size'),
        ('same_size_flip', lambda r: (r / 'review.md').write_bytes(b'!' + (r / 'review.md').read_bytes()[1:]), 'payload hash'),
        ('missing_payload', lambda r: (r / 'review.md').unlink(), 'exact sealed membership'),
        ('extra_payload', lambda r: (r / 'EXTRA').write_text('unexpected'), 'exact sealed membership'),
        ('edited_manifest', lambda r: (r / 'MANIFEST.json').write_bytes((r / 'MANIFEST.json').read_bytes() + b'\n'), 'external manifest anchor'),
        ('symlink', lambda r: replace_link(r, False), 'regular single-link payload'),
        ('hardlink', lambda r: replace_link(r, True), 'regular single-link payload'),
        ('transient_excluded', lambda r: add_transient(r), 'PASS'),
    ]
    rows = []
    tmp = HERE / 'tmp'
    tmp.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='verifier-controls-', dir=tmp) as td:
        for name, mutation, expected in cases:
            dst = Path(td) / name
            shutil.copytree(HERE, dst, ignore=shutil.ignore_patterns('tmp'))
            if mutation:
                mutation(dst)
            anchor = ('0' if a.anchor[0] != '0' else '1') + a.anchor[1:] if name == 'wrong_anchor' else a.anchor
            before = snapshot(dst)
            run = subprocess.run([sys.executable, '-I', '-B', str(dst / 'verify.py'), '--anchor', anchor],
                                 text=True, capture_output=True)
            output = run.stdout + run.stderr
            assert (run.returncode == 0) == (expected == 'PASS'), (name, output)
            assert expected in output, (name, expected, output)
            assert snapshot(dst) == before, ('verifier wrote files', name)
            rows.append({'case': name, 'expected': expected, 'exit_code': run.returncode,
                         'matched': True, 'read_only': True})
    print(json.dumps({'scope': 'integrity controls only', 'cases': rows}, indent=2))

def snapshot(root):
    out = {}
    for p in root.rglob('*'):
        if p.is_file() and not p.is_symlink():
            out[str(p.relative_to(root))] = hashlib.sha256(p.read_bytes()).hexdigest()
    return out

def replace_link(root, hard):
    file = root / 'review.md'
    content = root / 'tmp' / 'content.tex'
    content.parent.mkdir()
    content.write_bytes(file.read_bytes())
    file.unlink()
    if hard:
        os.link(content, file)
    else:
        file.symlink_to(content)

def add_transient(root):
    (root / 'tmp').mkdir()
    (root / 'tmp' / 'scratch.log').write_text('explicitly outside sealed membership')

if __name__ == '__main__':
    main()
