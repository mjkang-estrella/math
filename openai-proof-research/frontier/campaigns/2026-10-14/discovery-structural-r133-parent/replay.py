#!/usr/bin/env python3
"""Detached evidence intake for structural r133; copied integrity cases only, no mathematical gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile

FINAL = '28c1114b783e345e666741df7eadeecccdf6ae92aff898adf4a778b06624d832'
MANIFEST = 'a14d03fcc107582ad645e175e83ed765974805313e43e1958801088a6011cdaa'
REPORT = '86aa4c953e63da33ec5e7f2263b60df460cf122be84cf9337511cdb1e3f99643'


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
    author = parent.parent / 'fresh-structural-discovery-r133'
    repo = author.parents[3]
    assert sha(author / 'FINAL.json') == FINAL
    assert sha(author / 'packet/MANIFEST.json') == MANIFEST
    assert sha(author / 'REPORT.md') == REPORT
    assert sha(author / "packet/public/frozen-statement.md") == "72654d283495baa80aba6349b1b5ebb9a4634ba268d7499a6187ecdd1e311256"
    before = snapshot(author)
    original_verify = run(["python", "-B", "packet/public/verify.py", "--root", ".", "--project", str(repo), "--finalhash", FINAL], author)
    with tempfile.TemporaryDirectory(prefix='r133-intake-') as td:
        copy = Path(td) / 'root'; shutil.copytree(author, copy, symlinks=True)
        verify = run(['python', '-B', 'packet/public/verify.py', '--root', '.', '--project', str(repo), '--finalhash', FINAL], copy)
        wrong = run(['python', '-B', 'packet/public/verify.py', '--root', '.', '--project', str(repo), '--finalhash', '0' * 64], copy)
        controls = run(['python', '-B', 'packet/public/controls.py', '--root', '.', '--project', str(repo), '--finalhash', FINAL], copy)
    after = snapshot(author)
    out = dict(original_verify=original_verify, verify=verify, wrong_final=wrong, controls=controls,
               verify_ok=verify['exit'] == 0 and original_verify['exit'] == 0, wrong_final_rejected=wrong['exit'] != 0,
               controls_ok=controls['exit'] == 0, original_unchanged=before == after)
    (parent / 'replay.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k.endswith(('ok', 'rejected', 'unchanged'))}))


if __name__ == '__main__':
    main()
