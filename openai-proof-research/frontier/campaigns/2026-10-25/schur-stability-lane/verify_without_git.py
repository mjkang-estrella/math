#!/usr/bin/env python3
"""Run the unchanged campaign verifier without invoking the git executable.

The two read-only Git metadata queries are implemented with Dulwich. Its optional
index refresh is explicitly disabled. Every compilation and declaration/axiom
check is the unchanged campaign implementation in verify_outcome.py.
"""
import importlib.util
from pathlib import Path
import sys
root = Path(__file__).resolve().parent
sys.path.insert(0, str(root / 'tools/python'))
from dulwich.repo import Repo
from dulwich import porcelain
spec = importlib.util.spec_from_file_location('campaign_verifier', root / 'verify_outcome.py')
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
original_run = verifier.run

def run(command, **kwargs):
    command = list(map(str, command))
    if command[0] != 'git':
        return original_run(command, **kwargs)
    if command[1] != '-C':
        raise RuntimeError('Unexpected metadata query')
    with Repo(command[2]) as repo:
        if command[3:] == ['rev-parse', 'HEAD']:
            return repo.head().decode() + '\n'
        if command[3:] == ['status', '--porcelain', '--untracked-files=no']:
            status = porcelain.status(repo, untracked_files='no', optional_locks=False)
            if status.unstaged or any(status.staged.values()):
                return repr(status) + '\n'
            return ''
    raise RuntimeError('Unsupported metadata query')

verifier.run = run
verifier.main()
