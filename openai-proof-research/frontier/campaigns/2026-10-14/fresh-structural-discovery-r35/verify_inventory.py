#!/usr/bin/env python3
"""Verify an externally anchored recovery inventory, never a mathematical claim."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_relative(value):
    require(isinstance(value, str) and bool(value), 'empty/nonstring path')
    p = PurePosixPath(value)
    require(not p.is_absolute() and '..' not in p.parts and str(p) == value,
            'unsafe or noncanonical path: ' + value)
    return value


def verify(root, expected):
    require(bool(re.fullmatch('[0-9a-f]{64}', expected)), 'expected anchor must be lowercase SHA256')
    require(not root.is_symlink(), 'root may not be a symlink')
    root = root.resolve(strict=True)
    manifest_path = root / 'MANIFEST.json'
    require(not manifest_path.is_symlink(), 'manifest may not be a symlink')
    raw = manifest_path.read_bytes()
    require(sha(raw) == expected, 'manifest anchor mismatch')
    manifest = json.loads(raw)
    require(manifest['schema'] == 'structural-r35-recovery-inventory-v1', 'unknown schema')
    require(manifest['excluded_paths'] == ['MANIFEST.json'], 'unexpected exclusions')
    entries = manifest['files']
    names = [safe_relative(x['path']) for x in entries]
    require(len(set(names)) == len(names), 'duplicate manifest path')
    actual = []
    for path in root.rglob('*'):
        require(not path.is_symlink(), 'symlink present: ' + str(path.relative_to(root)))
        require(path.is_file() or path.is_dir(), 'special file present')
        if path.is_file() and path != manifest_path:
            actual.append(path.relative_to(root).as_posix())
    require(set(names) == set(actual), 'exact file inventory mismatch')
    for entry in entries:
        data = (root / entry['path']).read_bytes()
        require(len(data) == entry['size'] and sha(data) == entry['sha256'],
                'file identity mismatch: ' + entry['path'])
    original = json.loads((root / 'recovery-original-inventory.json').read_text())
    for entry in original['files']:
        name = safe_relative(entry['path'])
        data = (root / name).read_bytes()
        require(len(data) == entry['size'] and sha(data) == entry['sha256'],
                'original bytes changed: ' + name)
    upstream = json.loads((root / 'recovery-context/upstream.json').read_text())
    revision = upstream['commit']
    require(revision == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'wrong upstream revision')
    tree = json.loads((root / 'recovery-context/preprints-tree.json').read_text())
    require(tree.get('truncated') is False, 'source tree is truncated/unknown')
    lookup = {x['path']: x for x in tree['tree']}
    sources = json.loads((root / 'source-receipts.json').read_text())
    for entry in sources:
        name = safe_relative(entry['local'])
        data = (root / name).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(len(data) == entry['size'] and sha(data) == entry['sha256'], 'source receipt mismatch')
        require(blob == entry['git_blob'] == lookup[entry['path']]['sha'], 'source Git identity mismatch')
        require(entry['url'] == 'https://raw.githubusercontent.com/openai/math/' + revision + '/' + entry['path'],
                'source pinned URL mismatch')
    primaries = json.loads((root / 'primary-receipts.json').read_text())
    for entry in primaries:
        data = (root / safe_relative(entry['path'])).read_bytes()
        require(len(data) == entry['size'] and sha(data) == entry['sha256'], 'primary receipt mismatch')
    return {'status': 'PASS', 'manifest_sha256': expected, 'files': len(entries),
            'original_files_preserved': len(original['files']),
            'pinned_source_identities': len(sources), 'primary_body_identities': len(primaries),
            'mathematical_acceptance': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-manifest-sha256', required=True)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        result = verify(args.root, args.expected_manifest_sha256)
    except (ValueError, KeyError, TypeError, OSError) as error:
        print(json.dumps({'status': 'FAIL', 'error': str(error)}), file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
