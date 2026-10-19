#!/usr/bin/env python3
"""Detached evidence intake for analytic r128; copied integrity cases only, no mathematical gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile

FINAL = '4d2f418b25b547247c3def14f9eb20392b38052e19957fd19eac070a7fbc4ec9'
MANIFEST = 'f0c480386f172f16e952fa249f53b34cd81bfb9ae469052e827b9e5846c3325c'
REPORT = 'c0ee9db65759c394ff7e2b6cebc1c9738196f756487d04275fb12d1f49a4e1ec'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    result = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat(); value = [s.st_mode, s.st_nlink]
        if stat.S_ISREG(s.st_mode): value += [s.st_size, sha(p)]
        elif stat.S_ISLNK(s.st_mode): value += [os.readlink(p)]
        result[p.relative_to(root).as_posix()] = value
    return result


def run(args, cwd):
    r = subprocess.run(args, capture_output=True, text=True, cwd=cwd,
                       env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    return dict(exit=r.returncode, stdout=r.stdout[-4000:], stderr=r.stderr[-4000:])


def main():
    parent = Path(__file__).resolve().parent
    author = parent.parent / 'fresh-analytic-discovery-r128'
    repo = author.parents[3]
    assert sha(author / 'FINAL.json') == FINAL
    assert sha(author / 'packet/MANIFEST.json') == MANIFEST
    assert sha(author / 'REPORT.md') == REPORT
    before = snapshot(author)
    with tempfile.TemporaryDirectory(prefix='r128a-intake-') as td:
        copy = Path(td) / 'root'; shutil.copytree(author, copy, symlinks=True)
        tree = str(repo / 'sources/preprints-tree.json')
        args = ['--root', str(copy), '--report-sha256', REPORT]
        verify = run(['python3', '-B', 'packet/public/verify.py', *args, '--final-sha256', FINAL], copy)
        wrong = run(['python3', '-B', 'packet/public/verify.py', *args, '--final-sha256', '0' * 64], copy)
        controls = run(['python3', '-B', 'packet/public/controls.py', *args, '--final-sha256', FINAL], copy)
    after = snapshot(author)
    out = dict(verify=verify, wrong_final=wrong, controls=controls,
               verify_ok=verify['exit'] == 0, wrong_final_rejected=wrong['exit'] != 0,
               controls_ok=controls['exit'] == 0, original_unchanged=before == after)
    (parent / 'replay.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k.endswith(('ok', 'rejected', 'unchanged'))}))


if __name__ == '__main__':
    main()
