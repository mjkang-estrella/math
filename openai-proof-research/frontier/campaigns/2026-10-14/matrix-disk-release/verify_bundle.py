#!/usr/bin/env python3
"""Verify an extracted package and rerun its finite exact checks in a copy.

Copyright 2026 Myeongjin Kang. MIT; see ../matrix-disk-manuscript/LICENSE-code.txt.
Artifact and finite-algebra verification only, not analytic-proof checking.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[4]
CAMPAIGN = Path('frontier/campaigns/2026-10-14')


def verify():
    manifest = json.loads((ROOT / 'BUNDLE-MANIFEST.json').read_text())
    for name, expected in manifest['files'].items():
        relative = PurePosixPath(name)
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError(f'Unsafe manifest path: {name}')
        path = ROOT / relative
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(ROOT):
            raise ValueError(f'Nonregular package file: {name}')
        data = path.read_bytes()
        if len(data) != expected['bytes'] or hashlib.sha256(data).hexdigest() != expected['sha256']:
            raise ValueError(f'Package integrity mismatch: {name}')
    with tempfile.TemporaryDirectory(prefix='matrix-disk-checks-') as directory:
        dest = Path(directory) / 'checks'
        original = ROOT / CAMPAIGN / 'matrix-disk-manuscript/checks'
        shutil.copytree(original, dest)
        for script, receipt in [('discovery/check.py', 'discovery/checks.json'),
                                ('reviewer/supplemental-check.py', 'reviewer/supplemental-checks.json')]:
            expected = (original / receipt).read_bytes()
            subprocess.run([sys.executable, '-I', str(dest / script)], check=True, cwd=dest)
            if (dest / receipt).read_bytes() != expected:
                raise ValueError(f'Exact-check receipt changed: {receipt}')
    print(json.dumps({'status': 'PASS', 'project_files': len(manifest['files']),
                      'exact_checks': 33, 'analytic_proof_certified': False,
                      'full_Lean_certificate': False}))


if __name__ == '__main__':
    verify()
