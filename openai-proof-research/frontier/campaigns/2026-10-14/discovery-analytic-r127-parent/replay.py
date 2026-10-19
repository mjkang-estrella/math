#!/usr/bin/env python3
"""Detached evidence intake for analytic r127 (T372L127); copied integrity cases only, no mathematical gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile

FINAL = 'bf1f7e54da87fa799201fa78c30a45bec7fdee6631ff14e9aaf78f66aa30c15f'
MANIFEST = 'a48867c451ac1ebf79fc6fdf38472a7a39873f6346620f305a9e43c1e0b65af3'
REPORT = '97d95dbb2fca982fec5e09fbb64409e296ca6889088693967a04761105cc0e86'
FROZEN = '6e39d59e65aecf9fc8710244c7eccbe7964e38af10287ad173663585539d790a'
RECEIPT = '3496fe34cc3c13bc578cdcc2889b909727563915ec452a7e390292c4e84cfc7a'


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
    author = parent.parent / 'fresh-analytic-discovery-r127'
    assert sha(author / 'FINAL.json') == FINAL
    assert sha(author / 'packet/MANIFEST.json') == MANIFEST
    assert sha(author / 'REPORT.md') == REPORT
    assert sha(author / 'packet/public/frozen-scope.md') == FROZEN
    assert sha(author / 'controls/receipt.json') == RECEIPT
    before = snapshot(author)
    with tempfile.TemporaryDirectory(prefix='r127-intake-') as td:
        copy = Path(td) / 'root'; shutil.copytree(author, copy, symlinks=True)
        verify = run(['python3', '-B', 'packet/public/verify.py', '--root', '.', '--final-hash', FINAL, '--report-hash', REPORT], copy)
        wrong = run(['python3', '-B', 'packet/public/verify.py', '--root', '.', '--final-hash', '0' * 64, '--report-hash', REPORT], copy)
        controls = run(['python3', '-B', 'controls/run_controls.py'], copy)
    after = snapshot(author)
    out = dict(verify=verify, wrong_final=wrong, controls=controls,
               verify_ok=verify['exit'] == 0, wrong_final_rejected=wrong['exit'] != 0,
               controls_ok=controls['exit'] == 0, original_unchanged=before == after)
    (parent / 'replay.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k.endswith(('ok', 'rejected', 'unchanged'))}))


if __name__ == '__main__':
    main()
