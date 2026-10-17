#!/usr/bin/env python3
"""Read-only private discovery-packet integrity verifier. MIT, Myeongjin Kang 2026."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(name):
    q = PurePosixPath(name)
    if q.is_absolute() or '..' in q.parts or str(q) != name:
        raise ValueError('unsafe path')
    return name


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal-sha256', required=True)
    parser.add_argument('--source-tree', type=Path, default=Path(__file__).resolve().parents[4] / 'sources/preprints-tree.json')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    seal = root / 'manifest.json'
    if seal.is_symlink() or sha(seal.read_bytes()) != args.seal_sha256:
        raise ValueError('external manifest anchor mismatch')
    m = json.loads(seal.read_text())
    entries = list(root.rglob('*'))
    if any(p.is_symlink() for p in entries):
        raise ValueError('symlink rejected')
    files = {p.relative_to(root).as_posix() for p in entries if p.is_file()}
    dirs = {p.relative_to(root).as_posix() for p in entries if p.is_dir()}
    if files != set(m['files']) | {'manifest.json'} or dirs != set(m['directories']):
        raise ValueError('exact membership mismatch')
    for name, digest in m['files'].items():
        if sha((root / safe(name)).read_bytes()) != digest:
            raise ValueError('payload hash mismatch: ' + name)
    tree_bytes = args.source_tree.read_bytes()
    if sha(tree_bytes) != m['source_tree_sha256']:
        raise ValueError('source tree identity mismatch')
    tree = json.loads(tree_bytes)
    if tree.get('truncated') is not False:
        raise ValueError('complete source tree required')
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    count = 0
    for receipt in sorted(root.glob('source*-receipt.json')):
        for row in json.loads(receipt.read_text()):
            body = (root / safe(row['local'])).read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest()
            if sha(body) != row['sha256'] or blob != row['git_blob'] or blob != blobs[row['path']]:
                raise ValueError('source receipt mismatch: ' + row['path'])
            expected = 'https://raw.githubusercontent.com/openai/math/' + m['source_pin'] + '/' + row['path']
            if row['url'] != expected:
                raise ValueError('pinned URL mismatch')
            count += 1
    primary = json.loads((root / 'private/primary-receipts.json').read_text())
    for row in primary:
        body = (root / safe(row.get('local', row.get('file')))).read_bytes()
        if sha(body) != row['sha256'] or len(body) != row['bytes']:
            raise ValueError('primary receipt mismatch')
    print(json.dumps({'integrity': 'PASS', 'payload_files': len(m['files']), 'directories': len(dirs), 'source_blobs': count, 'primary_receipts': len(primary), 'mathematical_verdict': None, 'nominee': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        raise SystemExit('REJECT: ' + str(error))
