#!/usr/bin/env python3
"""MIT. Read-only byte/inventory verifier. Integrity is not mathematical proof."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_regular(path):
    s = path.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
        raise ValueError('not an ordinary single-link file: '+str(path))
    return path.read_bytes()


def safe(root, name):
    q = PurePosixPath(name)
    if q.is_absolute() or not q.parts or any(x in ('', '.', '..') for x in q.parts):
        raise ValueError('unsafe relative path')
    p = root
    for part in q.parts:
        p = p / part
        if p.is_symlink():
            raise ValueError('symlink: '+str(p))
    return p


def verify(root, expected, private=False, tree_path=None):
    if not re.fullmatch('[0-9a-f]{64}', expected):
        raise ValueError('a detached lowercase SHA256 is required')
    raw = read_regular(root/'manifest.json')
    if digest(raw) != expected:
        raise ValueError('external manifest anchor mismatch')
    m = json.loads(raw)
    if m['schema'] != 'r73-integrity-v1' or m['pinned_revision'] != 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb':
        raise ValueError('unexpected schema or pin')
    files = m['public_files']
    if len(files) != len({x['path'] for x in files}):
        raise ValueError('duplicate inventory path')
    wanted = {x['path'] for x in files}
    if any(x.startswith('private/') or x in ('manifest.json', 'manifest.sha256') for x in wanted):
        raise ValueError('invalid public inventory')
    actual = set()
    for p in root.rglob('*'):
        rel = p.relative_to(root).as_posix()
        if rel == 'private' or rel.startswith('private/'):
            continue
        if p.is_symlink():
            raise ValueError('public symlink')
        if p.is_file() and rel not in ('manifest.json', 'manifest.sha256'):
            actual.add(rel)
    if actual != wanted:
        raise ValueError('public inventory differs: '+str(sorted(actual ^ wanted)))
    for x in files:
        data = read_regular(safe(root, x['path']))
        if len(data) != x['bytes'] or digest(data) != x['sha256']:
            raise ValueError('public bytes differ: '+x['path'])
    # The sidecar is convenience only; it is never accepted as the trust anchor.
    if (root/'manifest.sha256').exists():
        if read_regular(root/'manifest.sha256').decode().strip() != expected:
            raise ValueError('sidecar differs from supplied anchor')
    sources = json.loads(read_regular(root/'source-receipts.json'))
    primary = json.loads(read_regular(root/'primary-receipts.json'))
    matched = 0
    if tree_path:
        raw_tree = read_regular(Path(tree_path))
        if digest(raw_tree) != m['canonical_tree']['sha256']:
            raise ValueError('external canonical tree hash differs')
        tree = json.loads(raw_tree)
        if tree.get('truncated') is not False or len(tree['tree']) != 13223:
            raise ValueError('not the complete canonical tree')
        blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
        for x in sources:
            if blobs.get(x['path']) != x['git_blob']:
                raise ValueError('source blob absent/different in canonical tree')
            required = 'https://raw.githubusercontent.com/openai/math/'+m['pinned_revision']+'/'+x['path']
            if x['url'] != required:
                raise ValueError('source URL is not pinned')
            matched += 1
    private_files = 0
    if private:
        if not tree_path:
            raise ValueError('--check-private also requires --canonical-tree')
        for x in sources:
            if not x['local'].startswith('private/'):
                raise ValueError('source body is not private')
            data = read_regular(safe(root, x['local']))
            blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            if digest(data) != x['sha256'] or blob != x['git_blob'] or len(data) != x['bytes']:
                raise ValueError('private source bytes differ')
            private_files += 1
        for x in primary:
            if not x['local'].startswith('private/'):
                raise ValueError('primary body is not private')
            pdf = safe(root, x['local'])
            if digest(read_regular(pdf)) != x['sha256']:
                raise ValueError('private primary PDF differs')
            if digest(read_regular(pdf.with_suffix('.txt'))) != x['text_sha256']:
                raise ValueError('private primary text differs')
            private_files += 2
    return {'integrity': 'verified', 'manifest_sha256': expected,
            'public_files': len(files), 'canonical_source_blobs': matched,
            'private_files_checked': private_files,
            'mathematics': 'not assessed', 'independent_gates': 'not performed',
            'campaign_credit': 0}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--expected-manifest-sha256', required=True)
    p.add_argument('--canonical-tree')
    p.add_argument('--check-private', action='store_true')
    args = p.parse_args()
    root = Path(__file__).absolute().parent
    try:
        result = verify(root, args.expected_manifest_sha256, args.check_private, args.canonical_tree)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({'integrity': 'REJECTED', 'reason': str(error)}))
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == '__main__':
    sys.exit(main())
