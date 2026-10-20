#!/usr/bin/env python3
"""Detached evidence intake for structural r131; copied integrity cases only, no mathematical gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile

FINAL = '0b40254423b4882d35d9dd028896c460fe067a99b1e316528051f679ca519a70'
MANIFEST = '594ce3eda942a247a86ed310565de8a7fdd8ae8e5051388f3e53e1f47f9c2a20'
REPORT = '78fab3419150b84980c6601f5c89956f5746f6a968686ccaa4b5785fc8d940eb'


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
    author = parent.parent / 'fresh-structural-discovery-r131'
    repo = author.parents[3]
    assert sha(author / 'FINAL.json') == FINAL
    assert sha(author / 'packet/MANIFEST.json') == MANIFEST
    assert sha(author / 'REPORT.md') == REPORT
    before = snapshot(author)
    with tempfile.TemporaryDirectory(prefix='r131-intake-') as td:
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
