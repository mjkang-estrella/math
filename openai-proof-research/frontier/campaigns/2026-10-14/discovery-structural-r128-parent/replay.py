#!/usr/bin/env python3
"""Detached evidence intake for structural r128; copied integrity cases only, no mathematical gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile

FINAL = 'd6e2b050e104278933b100a79deb1c3f0ea09d38f708b4d61792aedccb9889b0'
MANIFEST = 'ddb0f3f1e2e5eb968db26261fcee99fbd5d6aa8294ac26a6b158ba1f9ead5e9f'
REPORT = 'f0b6060fda9d7a76ffcf395d9d605ffb1ba5dfae903fbbd5c7ac62030cfa1b25'


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
    author = parent.parent / 'fresh-structural-discovery-r128'
    repo = author.parents[3]
    assert sha(author / 'FINAL.json') == FINAL
    assert sha(author / 'packet/MANIFEST.json') == MANIFEST
    assert sha(author / 'REPORT.md') == REPORT
    before = snapshot(author)
    with tempfile.TemporaryDirectory(prefix='r128-intake-') as td:
        copy = Path(td) / 'root'; shutil.copytree(author, copy, symlinks=True)
        verify = run(['python', '-B', 'packet/public/verify.py', '--root', '.', '--project', str(repo), '--finalhash', FINAL], copy)
        wrong = run(['python', '-B', 'packet/public/verify.py', '--root', '.', '--project', str(repo), '--finalhash', '0' * 64], copy)
        controls = run(['python', '-B', 'packet/public/controls.py', '--root', '.', '--project', str(repo), '--finalhash', FINAL], copy)
    after = snapshot(author)
    out = dict(verify=verify, wrong_final=wrong, controls=controls,
               verify_ok=verify['exit'] == 0, wrong_final_rejected=wrong['exit'] != 0,
               controls_ok=controls['exit'] == 0, original_unchanged=before == after)
    (parent / 'replay.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k.endswith(('ok', 'rejected', 'unchanged'))}))


if __name__ == '__main__':
    main()
