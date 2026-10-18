#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Read-only exact-inventory verifier for the ANS263 contribution review r1.

Integrity only: it does not check any mathematical or contribution verdict.
Usage: python3 -B verify.py --anchor <SHA256 of this directory's manifest.json>
"""
import argparse, hashlib, json, os, stat, subprocess, sys
from pathlib import Path, PurePosixPath

AUTHOR_ANCHOR = '0e1af1b06709a0585a8724e3a15e59e228a65f4c88ee363ef88e7aa482c73cf2'
PROOF_SHA = 'eef51e8d50cfaf29c971e346cc4f2957f40dfe033bda3de3d2543586879c7a48'
SCOPE_SHA = '03dd0d2eb2987fbc87bf130b7fe1978caa1755e7eb0286f616fc6ccfe13cf5fc'


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def digest(b):
    return hashlib.sha256(b).hexdigest()


def safe(s):
    p = PurePosixPath(s)
    require(isinstance(s, str) and str(p) == s and not p.is_absolute()
            and '..' not in p.parts and s not in ('', '.'), 'unsafe path ' + repr(s))


def inventory(root, skip_manifest=True):
    files, dirs = {}, []
    for base, ds, fs in os.walk(root, followlinks=False):
        for n in ds + fs:
            p = Path(base) / n
            st = p.lstat()
            rel = p.relative_to(root).as_posix()
            require(not stat.S_ISLNK(st.st_mode), 'symlink: ' + rel)
            if stat.S_ISDIR(st.st_mode):
                dirs.append(rel)
                continue
            require(stat.S_ISREG(st.st_mode), 'nonregular: ' + rel)
            require(st.st_nlink == 1, 'hardlink: ' + rel)
            if skip_manifest and rel == 'manifest.json':
                continue
            b = p.read_bytes()
            files[rel] = {'bytes': len(b), 'sha256': digest(b)}
    return files, sorted(dirs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    ns = ap.parse_args()
    require(len(ns.anchor) == 64 and all(c in '0123456789abcdef' for c in ns.anchor),
            'anchor must be lowercase SHA256')
    root = Path(__file__).absolute().parent
    for p in [root] + list(root.parents):
        require(not p.is_symlink(), 'symlink root/ancestor')
    mp = root / 'manifest.json'
    require(mp.is_file() and not mp.is_symlink() and mp.stat().st_nlink == 1, 'unsafe manifest')
    raw = mp.read_bytes()
    require(digest(raw) == ns.anchor, 'external anchor mismatch')
    m = json.loads(raw)
    require(m.get('schema') == 'ans263-contribution-r1-inventory-v1', 'schema')
    for s in m['files']:
        safe(s); require(s != 'manifest.json', 'self entry')
    for s in m['directories']:
        safe(s)
    files, dirs = inventory(root)
    require(files == m['files'], 'exact file inventory/hash mismatch')
    require(dirs == m['directories'], 'exact directory inventory mismatch')
    # Simulated membership rejection (non-mutating).
    for sim in ({**files, '__extra__': {'bytes': 0, 'sha256': ''}}, dict(list(files.items())[1:])):
        require(sim != m['files'], 'selfcheck failed to reject altered inventory')
    # Author packet binding, read-only reimplementation (author code not executed).
    author = root.parent / 'fresh-analytic-discovery-r32'
    araw = (author / 'manifest.json').read_bytes()
    require(digest(araw) == AUTHOR_ANCHOR, 'author manifest anchor changed')
    am = json.loads(araw)
    afiles, adirs = inventory(author)
    require(afiles == am['files'] and adirs == am['directories'], 'author inventory mismatch')
    require(afiles['263-working-proof.md']['sha256'] == PROOF_SHA, 'author proof changed')
    require(afiles['263-scope.md']['sha256'] == SCOPE_SHA, 'author scope changed')
    binding = json.loads((root / 'input-binding.json').read_text())
    for row in binding['files']:
        p = root.parent / row['path']
        b = p.read_bytes()
        require(digest(b) == row['sha256'] and len(b) == row['bytes'], 'bound input changed: ' + row['path'])
    # Replay reviewer arithmetic (exact rationals; nonproof).
    out = subprocess.run([sys.executable, '-B', '-I', str(root / 'checks/budget_alternatives.py')],
                         check=True, capture_output=True, text=True).stdout
    require(json.loads(out) == json.loads((root / 'checks/budget_alternatives.out').read_text()),
            'reviewer arithmetic replay changed')
    print(json.dumps({'status': 'PASS_INTEGRITY_ONLY', 'review_files': len(files),
                      'review_directories': len(dirs), 'author_payload_files': len(afiles),
                      'bound_inputs': len(binding['files']), 'arithmetic_replay': 'PASS_NONPROOF',
                      'verdict_recorded': 'TECHNICAL (not checked by this script)'}, indent=1))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
