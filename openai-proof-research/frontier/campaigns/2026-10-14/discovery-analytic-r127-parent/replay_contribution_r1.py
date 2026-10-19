#!/usr/bin/env python3
"""Detached intake of T372L127 contribution review r1; copied integrity cases only, no mathematical gate."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile

FINAL = '1b81dcb6a789c5caeb41aa77e66de24f79cb0b27db2178be9c0289fc0aa2f3a7'
MANIFEST = '8219a69b4bad57bd00c4c2ee962321cb2c02428c494c24c9796ca1dba9ca822f'
REPORT = 'b20c57c1a94ac3b0998b38cddb70dc5d5b6986fa03411016143965ce9127977a'


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
    review = parent.parent / 't372l127-contribution-r1'
    author = parent.parent / 'fresh-analytic-discovery-r127'
    assert sha(review / 'FINAL.json') == FINAL
    assert sha(review / 'MANIFEST.json') == MANIFEST
    assert sha(review / 'REPORT.md') == REPORT
    before, author_before = snapshot(review), snapshot(author)
    with tempfile.TemporaryDirectory(prefix='t372l127-contrib-') as td:
        copy = Path(td) / review.name; shutil.copytree(review, copy, symlinks=True)
        shutil.copytree(author, Path(td) / author.name, symlinks=True)
        common = ['--report-hash', REPORT]
        verify = run(['python3', '-B', 'public/verify.py', '--root', '.', '--author-root', str(author), '--final-hash', FINAL, *common], copy)
        wrong = run(['python3', '-B', 'public/verify.py', '--root', '.', '--author-root', str(author), '--final-hash', '0' * 64, *common], copy)
        controls = run(['python3', '-B', 'controls/run_controls.py', '--final-hash', FINAL, *common], copy)
    out = dict(verify=verify, wrong_final=wrong, controls=controls,
               verify_ok=verify['exit'] == 0, wrong_final_rejected=wrong['exit'] != 0,
               controls_ok=controls['exit'] == 0,
               review_unchanged=before == snapshot(review), author_unchanged=author_before == snapshot(author))
    (parent / 'contribution-r1-replay.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k.endswith(('ok', 'rejected', 'unchanged'))}))


if __name__ == '__main__':
    main()
