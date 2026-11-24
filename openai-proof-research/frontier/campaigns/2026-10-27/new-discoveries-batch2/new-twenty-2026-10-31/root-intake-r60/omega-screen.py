#!/usr/bin/env python3
"""Screen the public omega registry (the-omega-institute/trureturing) for prior resolutions.
Usage: omega-screen.py KEY [KEY ...]   (source arXiv ids, author surnames, distinctive terms)
Uses a sparse checkout of Blueprint, Library and docs; clones it if missing (a few minutes)."""
import subprocess, sys, os
from pathlib import Path
REPO = Path(os.environ.get('OMEGA_REPO', '/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/03704234-97d1-47f1-8192-8d8ee0dea55c/scratchpad/omega/repo'))
URL = 'https://github.com/the-omega-institute/trureturing'
def ensure():
    if not (REPO / 'Blueprint').is_dir():
        REPO.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['git', 'clone', '--depth', '1', '--filter=blob:none', '--no-checkout', URL, str(REPO)], check=True)
        subprocess.run(['git', 'sparse-checkout', 'init', '--cone'], cwd=REPO, check=True)
        subprocess.run(['git', 'sparse-checkout', 'set', 'Blueprint', 'Library', 'docs'], cwd=REPO, check=True)
        subprocess.run(['git', 'checkout'], cwd=REPO, check=True)
    return subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=REPO, capture_output=True, text=True).stdout.strip()
def screen(keys):
    head = ensure(); out = {}
    for k in keys:
        r = subprocess.run(['grep', '-rlF', '--include=*.md', k, 'Blueprint', 'Library'], cwd=REPO, capture_output=True, text=True)
        out[k] = [x for x in r.stdout.split('\n') if x]
    return head, out
if __name__ == '__main__':
    head, out = screen(sys.argv[1:])
    print('omega head', head)
    for k, fs in out.items(): print(repr(k), len(fs), fs[:5])
