#!/usr/bin/env python3
"""MIT, Myeongjin Kang. Read-only integrity/replay, not mathematical review."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent


def digest(p):
    b = p.read_bytes()
    return {'size': len(b), 'sha256': hashlib.sha256(b).hexdigest()}


def tree(p):
    result = []
    for q in sorted(p.rglob('*')):
        if q.is_symlink():
            raise ValueError('symlink forbidden: '+str(q))
        if q.is_file():
            result.append({'path': q.relative_to(p).as_posix(), **digest(q)})
    return result


def safe(root, s):
    q = Path(s)
    if q.is_absolute() or '..' in q.parts or not q.parts:
        raise ValueError('invalid relative inventory path')
    p = root/q
    if not p.resolve().is_relative_to(root.resolve()):
        raise ValueError('inventory escape')
    return p


def match(p, row):
    if digest(p) != {'size': row['size'], 'sha256': row['sha256']}:
        raise ValueError('size/hash mismatch: '+str(p))


def historical(t):
    root = Path(t['root'])
    if digest(root/'seal.json')['sha256'] != t['external_seal_sha256']:
        raise ValueError('historical external seal mismatch')
    if tree(root) != t['inventory']:
        raise ValueError('historical inventory mismatch')
    seal = json.loads((root/'seal.json').read_text())
    expected = {'seal.json', 'seal.sha256', 'inputs-manifest.json', 'outputs-manifest.json'}
    for name, row in seal['manifests'].items():
        match(safe(root, name), row)
        entries = json.loads((root/name).read_text())['files']
        for item in entries:
            p = safe(root, item['path'])
            match(p, item)
            if item['path'] in expected:
                raise ValueError('historical duplicate membership')
            expected.add(item['path'])
    if {x['path'] for x in t['inventory']} != expected:
        raise ValueError('historical exact membership mismatch')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal-sha256', required=True)
    parser.add_argument('--hash-only', action='store_true')
    args = parser.parse_args()
    # Whole-tree snapshots precede validation; even failed checks have no writes.
    before = tree(ROOT)
    external = json.loads((ROOT/'external-inputs.json').read_text())
    ext_before = {t['root']: tree(Path(t['root'])) for t in external['trees']}
    files_before = {x['path']: digest(Path(x['path'])) for x in external['files']}
    error = None
    result = None
    try:
        anchor = args.seal_sha256
        if not re.fullmatch('[0-9a-f]{64}', anchor):
            raise ValueError('malformed external seal anchor')
        if digest(ROOT/'seal.json')['sha256'] != anchor:
            raise ValueError('external seal anchor mismatch')
        detached = (ROOT/'seal.sha256').read_text()
        if detached not in (anchor+'\n', anchor+'  seal.json\n'):
            raise ValueError('detached seal record mismatch')
        seal = json.loads((ROOT/'seal.json').read_text())
        if set(seal['manifests']) != {'inputs-manifest.json', 'outputs-manifest.json'}:
            raise ValueError('manifest membership mismatch')
        expected = {'seal.json', 'seal.sha256', 'inputs-manifest.json', 'outputs-manifest.json'}
        counts = {}
        for name, row in seal['manifests'].items():
            match(ROOT/name, row)
            entries = json.loads((ROOT/name).read_text())['files']
            counts[name] = len(entries)
            for item in entries:
                if item['path'] in expected:
                    raise ValueError('duplicate inventory member')
                expected.add(item['path'])
                match(safe(ROOT, item['path']), item)
        if {x['path'] for x in before} != expected:
            raise ValueError('own exact membership mismatch')
        for t in external['trees']:
            historical(t)
        for row in external['files']:
            match(Path(row['path']), row)
        pin = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
        context = ROOT/'inputs/private/context'
        upstream = json.loads((context/'sources/upstream.json').read_text())
        if upstream['commit'] != pin or upstream['repository'] != 'https://github.com/openai/math':
            raise ValueError('upstream pin mismatch')
        catalogue = json.loads((context/'sources/preprints-tree.json').read_text())
        if catalogue['truncated'] or catalogue['sha'] != 'df0564b2deaab87e07854b6344d8c2f037682e77':
            raise ValueError('complete preprints tree mismatch')
        blobs = {e['path']: e['sha'] for e in catalogue['tree'] if e['type'] == 'blob'}
        retrievals = json.loads((ROOT/'retrievals.json').read_text())
        names = set()
        for row in retrievals:
            if row['path'] in names:
                raise ValueError('duplicate retrieved source')
            names.add(row['path'])
            p = safe(ROOT, row['path'])
            b = p.read_bytes()
            sha1 = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            if sha1 != row['git_blob_sha1'] or sha1 != blobs[row['upstream_path']]:
                raise ValueError('pinned Git blob mismatch')
            if len(b) != row['bytes'] or hashlib.sha256(b).hexdigest() != row['sha256']:
                raise ValueError('retrieved byte receipt mismatch')
            if row['url'] != 'https://raw.githubusercontent.com/openai/math/'+pin+'/'+row['upstream_path']:
                raise ValueError('unpinned source URL')
        if not args.hash_only:
            auth = json.loads((ROOT/'checker-preexecution.json').read_text())
            checker = ROOT/'hom_checks.py'
            match(checker, auth)
            # The runner and checker were both authenticated above before execution.
            runner = (ROOT/'readonly-runner.txt').read_text()
            p = subprocess.run([sys.executable, '-I', '-B', '-c', runner,
                                str(checker), auth['sha256']],
                               capture_output=True, timeout=30, cwd=ROOT)
            if p.returncode != 0:
                raise ValueError('authenticated checker failed: '+p.stderr.decode(errors='replace'))
            if p.stdout != (ROOT/'checks-receipt.json').read_bytes():
                raise ValueError('immutable checker stdout mismatch')
            if p.stderr != (ROOT/'checks.stderr').read_bytes():
                raise ValueError('immutable checker stderr mismatch')
        result = {'status': 'PASS_INTEGRITY_ONLY' if args.hash_only else 'PASS_INTEGRITY_AND_FINITE_SUPPORT_ONLY',
                  'target_status': 'UNRESOLVED', 'counted': False, 'accepted_count': 4,
                  'own_files': len(expected), 'input_files': counts['inputs-manifest.json'],
                  'output_files': counts['outputs-manifest.json'],
                  'pinned_git_blobs': len(retrievals),
                  'historical_files': sum(len(t['inventory']) for t in external['trees']),
                  'historical_code_executed': False, 'seal_sha256': anchor}
    except Exception as exc:
        error = str(exc)
    finally:
        if tree(ROOT) != before:
            raise RuntimeError('own frozen tree changed during verification')
        for root, inv in ext_before.items():
            if tree(Path(root)) != inv:
                raise RuntimeError('historical frozen tree changed during verification')
        for name, value in files_before.items():
            if digest(Path(name)) != value:
                raise RuntimeError('external fixed file changed during verification')
    if error is not None:
        print(json.dumps({'status': 'REJECT', 'error': error,
                          'frozen_trees_unchanged': True}, sort_keys=True))
        return 1
    result['frozen_trees_unchanged'] = True
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
