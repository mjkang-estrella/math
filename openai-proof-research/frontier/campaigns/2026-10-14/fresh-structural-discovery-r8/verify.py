#!/usr/bin/env python3
"""Read-only integrity/replay verifier; authenticate this file before running.
Myeongjin Kang; no affiliation. MIT. No inventory or receipt regeneration.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def sha(b):
    return hashlib.sha256(b).hexdigest()


def snapshot():
    """Whole package, including seals and directory names, without following links."""
    out = {}
    for parent, directories, files in os.walk(ROOT, followlinks=False):
        for name in sorted(directories+files):
            p = Path(parent)/name
            key = p.relative_to(ROOT).as_posix()
            if p.is_symlink():
                out[key] = ['symlink', os.readlink(p)]
            elif p.is_dir():
                out[key] = ['directory']
            elif p.is_file():
                b = p.read_bytes()
                out[key] = ['file', len(b), sha(b)]
            else:
                out[key] = ['special']
    return out


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read_entry(entry):
    s = entry['path']
    p = Path(s)
    require(not p.is_absolute() and p.as_posix() == s and '..' not in p.parts,
            'noncanonical manifest path')
    full = ROOT/p
    require(not full.is_symlink() and full.is_file(), 'not an ordinary file: '+s)
    b = full.read_bytes()
    require(len(b) == entry['size'] and sha(b) == entry['sha256'],
            'hash/size mismatch: '+s)
    return b


def verify(anchor, exercise_failure):
    require(len(anchor) == 64 and all(c in '0123456789abcdef' for c in anchor),
            'expected lowercase external SHA256')
    seal_bytes = (ROOT/'seal.json').read_bytes()
    require(sha(seal_bytes) == anchor, 'external detached seal mismatch')
    seal = json.loads(seal_bytes)
    require((ROOT/'seal.sha256').read_text() == anchor+'  seal.json\n',
            'detached seal file mismatch')
    inventories = []
    for name in ['inputs-manifest.json', 'outputs-manifest.json']:
        require(seal['manifests'][name]['path'] == name, 'wrong manifest name')
        inventories.append(json.loads(read_entry(seal['manifests'][name])))
    entries = inventories[0]['files']+inventories[1]['files']
    paths = [e['path'] for e in entries]
    require(len(paths) == len(set(paths)), 'overlapping inventory entries')
    require(all(p.startswith('inputs/') for p in
                [e['path'] for e in inventories[0]['files']]), 'input inventory scope')
    require(all(not e['path'].startswith('inputs/') for e in inventories[1]['files']),
            'output inventory scope')
    actual = snapshot()
    require(all(v[0] in ['file', 'directory'] for v in actual.values()),
            'links/special files are forbidden')
    expected = set(paths)|{'inputs-manifest.json', 'outputs-manifest.json',
                           'seal.json', 'seal.sha256'}
    require({p for p, v in actual.items() if v[0] == 'file'} == expected,
            'exact file inventory mismatch')
    for e in entries:
        read_entry(e)

    context = ROOT/'inputs/private/context'
    descriptor = json.loads((context/'sources/upstream.json').read_text())
    require(descriptor['commit'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
            'wrong upstream revision')
    tree = json.loads((context/'sources/preprints-tree.json').read_text())
    require(tree.get('truncated') is False, 'preprint tree is truncated')
    index = {v['path']: v for v in tree['tree']}
    records = json.loads((ROOT/'retrievals.json').read_text())
    for e in records:
        b = read_entry(e)
        blob = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(blob == e['git_blob'] == index[e['upstream_path']]['sha'],
                'pinned Git blob mismatch')
        require(e['url'] == 'https://raw.githubusercontent.com/openai/math/'+
                descriptor['commit']+'/'+e['upstream_path'], 'wrong raw source URL')
    require(len(records) == 10, 'unexpected pinned family inventory')
    lit = json.loads((ROOT/'literature-retrievals.json').read_text())
    for e in lit:
        read_entry(e)
    lp = ROOT/'inputs/private/literature'
    require(gzip.decompress((lp/'shareshian-wachs-source.bin').read_bytes()) ==
            (lp/'shareshian-wachs.tex').read_bytes(), 'gzip derivation mismatch')

    # All package bytes and source pins are authenticated before code execution.
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    replay = {}
    for program, receipt in [('checks.py', 'checks-receipt.txt'),
                             ('mutation_probe.py', 'mutation-receipt.txt')]:
        argv = [sys.executable, '-B', str(ROOT/program)]
        if exercise_failure and program == 'checks.py':
            argv.append('--exercise-failure-path')
        r = subprocess.run(argv, cwd='/', env=env, capture_output=True, timeout=120)
        require(r.returncode == 0, program+' failed: '+r.stderr.decode(errors='replace'))
        require(r.stderr == b'', program+' produced stderr')
        require(r.stdout == (ROOT/receipt).read_bytes(), program+' receipt mismatch')
        replay[program] = sha(r.stdout)
    return dict(status='PASS_INTEGRITY_AND_FINITE_SUPPORT_ONLY_U_UNRESOLVED',
                seal_sha256=anchor, input_files=len(inventories[0]['files']),
                output_files=len(inventories[1]['files']), pinned_git_blobs=len(records),
                replay=replay, independent_mathematical_pass=False, counted=False)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('expected_seal_sha256')
    parser.add_argument('--exercise-checker-failure', action='store_true')
    args = parser.parse_args()
    before = snapshot()
    result = None
    error = None
    try:
        result = verify(args.expected_seal_sha256, args.exercise_checker_failure)
    except Exception as e:
        error = str(e)
    finally:
        unchanged = snapshot() == before
    if not unchanged:
        error = 'FROZEN TREE CHANGED'+(' after: '+error if error else '')
    if error is not None:
        print(json.dumps(dict(status='REJECT', error=error,
                              frozen_tree_unchanged=unchanged), sort_keys=True))
        return 1
    result['frozen_tree_unchanged'] = unchanged
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
