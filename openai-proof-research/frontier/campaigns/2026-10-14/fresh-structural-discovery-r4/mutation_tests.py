#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT licensed; see RIGHTS.md.
"""Run verifier rejection controls ONLY on disposable package copies."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def run(root, seal):
    return subprocess.run([sys.executable, '-B', str(root/'verify.py'),
                           '--seal-sha256', seal], cwd=root, capture_output=True,
                          timeout=180)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal-sha256', required=True)
    args = parser.parse_args()
    baseline = run(ROOT, args.seal_sha256)
    assert baseline.returncode == 0, baseline.stderr.decode()
    baseline_members = [p for p in ROOT.rglob('*') if p.is_file()]
    outcomes = []
    with tempfile.TemporaryDirectory(prefix='.mutation-', dir=ROOT) as td:
        for case in ('receipt', 'input', 'missing', 'extra', 'checker_sentinel'):
            copy = Path(td)/case
            copy.mkdir()
            for p in baseline_members:
                dest = copy/p.relative_to(ROOT)
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(p, dest)
            if case == 'receipt':
                p = copy/'checks-receipt.json'
                p.write_bytes(p.read_bytes()+b' ')
            elif case == 'input':
                p = copy/'inputs/private/context/AGENTS.md'
                p.write_bytes(p.read_bytes()+b'\nmutation\n')
            elif case == 'missing':
                (copy/'candidate.md').unlink()
            elif case == 'extra':
                (copy/'unlisted.txt').write_text('mutation\n')
            else:
                p = copy/'checks.py'
                p.write_text("from pathlib import Path\nPath('SENTINEL').write_text('executed')\n")
            result = run(copy, args.seal_sha256)
            assert result.returncode != 0, case+' was wrongly accepted'
            assert not (copy/'SENTINEL').exists(), 'unauthenticated checker was executed'
            error = result.stderr.decode()
            assert ('authentication failed' in error or 'membership mismatch' in error), error
            outcomes.append(case)
    post = run(ROOT, args.seal_sha256)
    assert post.returncode == 0, post.stderr.decode()
    print(json.dumps({'status': 'PASS_disposable_copy_controls',
                      'rejected_mutations': outcomes,
                      'unauthenticated_checker_executed': False,
                      'original_reauthenticated_after_cleanup': True}, sort_keys=True))


if __name__ == '__main__':
    main()
