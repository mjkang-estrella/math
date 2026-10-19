#!/usr/bin/env python3
"""Detached evidence intake for arithmetic r94; copied integrity cases only, no mathematical gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile

FINAL = '14846105ba94423addc83b0b510bdf95321d523a99f3c052eda38a3ef0b70e59'
MANIFEST = 'c72773bde3b6e1e15ad803f40be14e98e1a3478ef12611af3d3de88ffdc4d685'
REPORT = '00e972798350864994478a677b0587a6723219c8f3bb308c696182792e73b4ef'


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
    author = parent.parent / 'fresh-arithmetic-discovery-r94'
    repo = author.parents[3]
    assert sha(author / 'FINAL.json') == FINAL
    assert sha(author / 'packet/MANIFEST.json') == MANIFEST
    assert sha(author / 'REPORT.md') == REPORT
    before = snapshot(author)
    with tempfile.TemporaryDirectory(prefix='r94-intake-') as td:
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
