#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Authenticate before subprocess execution; never import candidate/source code.
No writes, cache generation, network, receipt generation or unsafe archive loading.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys

R8_ANCHOR = '6db6112bf4297450c063652b5cc415d8a4f2d20b8b5138753349fcbafbfd3600'
METADATA = {'inputs-manifest.json', 'outputs-manifest.json', 'seal.json', 'seal.sha256'}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def need(condition, message):
    if not condition:
        raise ValueError(message)


def safe_file(root, name):
    path = PurePosixPath(name)
    need(bool(name) and not path.is_absolute() and '..' not in path.parts and str(path) == name,
         'invalid relative inventory path')
    target = root.joinpath(*path.parts)
    need(target.is_file() and not target.is_symlink(), 'missing/nonregular inventory file: '+name)
    need(target.resolve().is_relative_to(root.resolve()), 'inventory path escapes root')
    return target


def tree_state(root):
    need(root.is_dir() and not root.is_symlink(), 'missing/nonregular tree')
    entries = []
    for path in sorted(root.rglob('*')):
        need(not path.is_symlink(), 'symlink in frozen tree')
        if path.is_file():
            raw = path.read_bytes()
            entries.append((str(path.relative_to(root)), len(raw), sha(raw)))
    return sha(json.dumps(entries, separators=(',', ':')).encode())


def inventory(root, anchor):
    raw = safe_file(root, 'seal.json').read_bytes()
    need(sha(raw) == anchor, 'detached seal mismatch')
    seal = json.loads(raw)
    need(set(seal['manifests']) == {'inputs-manifest.json', 'outputs-manifest.json'}, 'wrong manifest set')
    need(safe_file(root, 'seal.sha256').read_text().split() == [anchor, 'seal.json'], 'detached anchor file mismatch')
    entries = {}
    counts = {}
    for name, info in seal['manifests'].items():
        data = safe_file(root, name).read_bytes()
        need(info['path'] == name and len(data) == info['size'] and sha(data) == info['sha256'], 'manifest mismatch: '+name)
        manifest = json.loads(data)
        counts[name] = len(manifest['files'])
        for entry in manifest['files']:
            rel = entry['path']
            need(rel not in entries and rel not in METADATA, 'duplicate/metadata inventory entry')
            content = safe_file(root, rel).read_bytes()
            need(len(content) == entry['size'] and sha(content) == entry['sha256'], 'inventory mismatch: '+rel)
            entries[rel] = entry
    actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    need(actual == set(entries) | METADATA, 'exact file inventory mismatch')
    return entries, counts


def provenance(root, r8):
    for path in (root/'inputs/private/r8').rglob('*'):
        if path.is_file():
            rel = str(path.relative_to(root/'inputs/private/r8'))
            need(path.read_bytes() == safe_file(r8, rel).read_bytes(), 'copied r8 mismatch: '+rel)
    original_maps = {}
    for name in ('inputs-manifest.json', 'outputs-manifest.json'):
        original_maps.update({x['path']: x for x in json.loads((r8/name).read_bytes())['files']})
    inherited = 0
    for path in (root/'inputs').rglob('*'):
        if not path.is_file():
            continue
        rel = str(path.relative_to(root))
        if rel in original_maps:
            entry = original_maps[rel]
            raw = path.read_bytes()
            need(len(raw) == entry['size'] and sha(raw) == entry['sha256'], 'inherited r8 byte mismatch')
            inherited += 1
    records = json.loads((root/'inputs/private/r8/retrievals.json').read_bytes())
    tree = json.loads((root/'inputs/private/context/sources/preprints-tree.json').read_bytes())
    need(not tree.get('truncated', True), 'source tree is truncated')
    lookup = {x['path']: x for x in tree['tree']}
    need(len(records) == 10, 'wrong pinned blob count')
    for record in records:
        raw = safe_file(root, record['path']).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        path = record['upstream_path']
        source = lookup.get(path, lookup.get(path.removeprefix('preprints/')))
        need(source is not None and source['sha'] == blob == record['git_blob'], 'pinned Git blob mismatch')
        need(sha(raw) == record['sha256'] and len(raw) == record['size'], 'pinned digest mismatch')
        need('/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in record['url'], 'unpinned upstream URL')
    return inherited


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seal', required=True, help='Externally trusted SHA256 of seal.json')
    parser.add_argument('--r8', type=Path, help='Original frozen r8 root; default is its campaign sibling')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    r8 = (args.r8 or root.parent/'fresh-structural-discovery-r8').resolve()
    need(root != r8 and not r8.is_relative_to(root), 'r8 must be a separate frozen tree')
    before = (tree_state(root), tree_state(r8))
    result = None
    failure = None
    try:
        _, r8counts = inventory(r8, R8_ANCHOR)
        _, counts = inventory(root, args.seal)
        inherited = provenance(root, r8)
        # Authenticated authored code only. Isolated stdlib, no site imports/cache.
        run = subprocess.run([sys.executable, '-I', '-B', '-S', str(root/'checks.py')],
                             cwd=root, capture_output=True, timeout=120, check=False)
        need(run.returncode == 0, 'authenticated checker failed (exit '+str(run.returncode)+')')
        need(run.stderr == b'', 'unexpected checker stderr')
        need(run.stdout == (root/'checks-receipt.txt').read_bytes(), 'immutable checker receipt mismatch')
        result = {'status': 'PASS_INTEGRITY_AND_SUPPORTING_ARITHMETIC_ONLY_U_UNRESOLVED',
                  'inputs': counts['inputs-manifest.json'], 'outputs': counts['outputs-manifest.json'],
                  'r8_inputs': r8counts['inputs-manifest.json'], 'r8_outputs': r8counts['outputs-manifest.json'],
                  'inherited_r8_inputs': inherited, 'pinned_git_blobs': 10,
                  'checker_stdout_sha256': sha(run.stdout), 'counted': False}
    except Exception as exc:
        failure = str(exc)
    finally:
        after = (tree_state(root), tree_state(r8))
        if before != after:
            failure = 'FROZEN TREE MODIFIED DURING VERIFICATION'
    if failure:
        print(json.dumps({'status': 'REJECTED', 'reason': failure, 'trees_unchanged': before == after}, sort_keys=True))
        return 1
    result['trees_unchanged'] = True
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as exc:
        print(json.dumps({'status': 'REJECTED_BEFORE_EXECUTION', 'reason': str(exc)}, sort_keys=True))
        sys.exit(1)
