#!/usr/bin/env python3
"""Detached evidence intake for arithmetic r95; copied integrity cases only, no mathematical gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile

FINAL = '52e95426ccaab6c817c23610322a55c2bd08ca657f36577f5632a1f9e4b3182f'
MANIFEST = '82237944d68b5ea200a72d8c7528c62cf8f8b3a64682c95e11430406b502bff6'
REPORT = 'c638d81b7da974615a71cc3b8dfb9f0ebe6560e83c29c6ccf32e84164c9a092f'


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
    author = parent.parent / 'fresh-arithmetic-discovery-r95'
    repo = author.parents[3]
    assert sha(author / 'FINAL.json') == FINAL
    assert sha(author / 'packet/MANIFEST.json') == MANIFEST
    assert sha(author / 'REPORT.md') == REPORT
    before = snapshot(author)
    with tempfile.TemporaryDirectory(prefix='r95-intake-') as td:
        copy = Path(td) / 'root'; shutil.copytree(author, copy, symlinks=True)
        tree = str(repo / 'sources/preprints-tree.json')
        args = ['--root', str(copy), '--tree', tree, '--report-sha256', REPORT]
        verify = run(['python3', '-B', 'packet/code/verify.py', *args, '--final-sha256', FINAL], copy)
        wrong = run(['python3', '-B', 'packet/code/verify.py', *args, '--final-sha256', '0' * 64], copy)
        controls = run(['python3', '-B', 'packet/code/controls.py', *args, '--final-sha256', FINAL], copy)
    after = snapshot(author)
    out = dict(verify=verify, wrong_final=wrong, controls=controls,
               verify_ok=verify['exit'] == 0, wrong_final_rejected=wrong['exit'] != 0,
               controls_ok=controls['exit'] == 0, original_unchanged=before == after)
    (parent / 'replay.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k.endswith(('ok', 'rejected', 'unchanged'))}))


if __name__ == '__main__':
    main()
