#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only identity check. Supply the manifest SHA256 from an external receipt."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

AUTHOR_MANIFEST = 'bde061c4eea5499343cfd07b623efe2079b858b19faa90f031e719702ec4902b'
CANDIDATE = '9ea51c98f9f50c7e614c754070b21ba8fc0e558df506363ccbbcaa453962ca80'
SCOPE = 'e40f0169ee9c301474c7f255ea129e311f001990786c338862e884dddf756e8f'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def require(test, message):
    if not test:
        raise SystemExit('FAIL: ' + message)

def safe_path(root, value):
    p = PurePosixPath(value)
    require(not p.is_absolute() and '..' not in p.parts and str(p) == value, 'unsafe path')
    return root / value

def authenticate(root, manifest_name, expected_hash):
    path = root / manifest_name
    require(not path.is_symlink(), 'manifest symlink')
    data = path.read_bytes()
    require(sha(data) == expected_hash, 'external manifest anchor mismatch')
    manifest = json.loads(data)
    rows = manifest['files']
    paths = [r['path'] for r in rows]
    require(len(paths) == len(set(paths)), 'duplicate payload path')
    require(manifest_name not in paths, 'manifest included in own payload')
    expected = set(paths) | {manifest_name}
    all_paths = list(root.rglob('*'))
    require(not any(p.is_symlink() for p in all_paths), 'symlink in packet')
    actual = {p.relative_to(root).as_posix() for p in all_paths if p.is_file()}
    require(actual == expected, 'exact file membership mismatch')
    expected_dirs = set()
    for item in paths:
        p = safe_path(root, item)
        for parent in p.relative_to(root).parents:
            if str(parent) != '.':
                expected_dirs.add(parent.as_posix())
    actual_dirs = {p.relative_to(root).as_posix() for p in all_paths if p.is_dir()}
    require(actual_dirs == expected_dirs, 'exact directory membership mismatch')
    for row in rows:
        b = safe_path(root, row['path']).read_bytes()
        require(len(b) == row['bytes'] and sha(b) == row['sha256'], 'payload mismatch: ' + row['path'])
    return manifest

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-sha256', required=True)
    args = parser.parse_args()
    require(len(args.manifest_sha256) == 64 and all(c in '0123456789abcdef' for c in args.manifest_sha256), 'invalid external SHA256')
    review = Path(__file__).resolve().parent
    own = authenticate(review, 'review-manifest.json', args.manifest_sha256)
    author = review.parent / 'fresh-analytic-discovery-r19'
    am = authenticate(author, 'sealed-manifest.json', AUTHOR_MANIFEST)
    require(len(am['files']) == 43, 'author payload count')
    require(sha((author / 'candidate.md').read_bytes()) == CANDIDATE, 'candidate anchor')
    require(sha((author / 'original-scope.md').read_bytes()) == SCOPE, 'scope anchor')
    audit = json.loads((review / 'source-authentication.json').read_text())
    repo = review.parents[3]
    catalog_data = safe_path(repo, audit['catalog_path']).read_bytes()
    require(sha(catalog_data) == audit['catalog_sha256'], 'catalog anchor')
    catalog = json.loads(catalog_data)
    require(catalog['truncated'] is False, 'truncated source catalog')
    blobs = {r['path']: r['sha'] for r in catalog['tree'] if r['type'] == 'blob'}
    sources = json.loads((author / 'source-receipt.json').read_text())
    sources.append(json.loads((author / 'companion-check-receipt.json').read_text()))
    require(sources == audit['checked_source_receipts'] and len(sources) == 27, 'source receipt mismatch')
    for row in sources:
        data = safe_path(author, row['local']).read_bytes()
        require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'source bytes')
        git_blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(git_blob == row['git_blob'] == blobs[row['path']], 'pinned blob mismatch')
        require('/' + PIN + '/' in row['url'], 'source URL pin')
    primary = json.loads((author / 'primary-receipt.json').read_text())
    require(primary == audit['primary_receipts'], 'primary receipt mismatch')
    count = 0
    for source in primary:
        for row in source['local_files']:
            data = safe_path(author, row['path']).read_bytes()
            require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'classical input bytes')
            count += 1
    require(count == 6, 'primary payload count')
    downloads = json.loads((review / 'private/primary-downloads.json').read_text())
    for row in downloads:
        data = safe_path(review / 'private', row['file']).read_bytes()
        require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'reviewer primary download')
    print(json.dumps({'status': 'PASS_IDENTITY_ONLY', 'verdict': own['verdict'], 'review_payloads': len(own['files']), 'author_payloads': 43, 'pinned_blobs': 27, 'author_primary_pdf_texts': 6, 'reviewer_primary_pdfs': len(downloads), 'proof_verdict': 'not supplied by contribution review'}, sort_keys=True))

if __name__ == '__main__':
    main()
