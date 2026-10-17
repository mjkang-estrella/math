#!/usr/bin/env python3
"""Read-only byte verifier; MIT, copyright 2026 Myeongjin Kang.
Required external anchor authenticates the manifest, not the review verdict.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def digest(b):
    return hashlib.sha256(b).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def check_packet(root, anchor, expected_format):
    require(not root.is_symlink(), 'symlink root')
    raw = (root / 'manifest.json').read_bytes()
    require(digest(raw) == anchor, 'manifest anchor mismatch')
    m = json.loads(raw)
    require(m['format'] == expected_format, 'wrong format')
    records = m['files']
    names = [r['path'] for r in records]
    require(len(names) == len(set(names)), 'duplicate path')
    for name in names:
        p = PurePosixPath(name)
        require(not p.is_absolute() and '..' not in p.parts and str(p) == name
                and name != 'manifest.json', 'unsafe path')
    files, dirs = set(), set()
    for p in root.rglob('*'):
        require(not p.is_symlink(), 'symlink entry')
        rel = p.relative_to(root).as_posix()
        if p.is_file():
            files.add(rel)
        elif p.is_dir():
            dirs.add(rel)
        else:
            raise ValueError('nonregular entry')
    require(files == set(names) | {'manifest.json'}, 'file inventory mismatch')
    require(dirs == set(m['directories']), 'directory inventory mismatch')
    data = {}
    for r in records:
        b = (root / r['path']).read_bytes()
        require(len(b) == r['bytes'] and digest(b) == r['sha256'],
                'payload changed: ' + r['path'])
        data[r['path']] = b
    return data


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest-sha256', required=True)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    owned = check_packet(root, args.manifest_sha256, 'cs-contribution-review-v1')
    binding = json.loads(owned['input-binding.json'])
    author = check_packet(root.parent / 'fresh-analytic-discovery-r18',
                          binding['author_manifest_sha256'], 'cs-review-packet-v1')
    for key in ['candidate.md', 'original-scope.md']:
        require(digest(author[key]) == binding['fixed_files'][key], 'frozen scope changed')
    sources = json.loads(author['source-receipt.json'])
    require(sources['commit'] == binding['pinned_revision'], 'pin mismatch')
    for r in sources['pinned_blobs_verified']:
        b = author[r['local']]
        git = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        require(git == r['git_blob'] and digest(b) == r['sha256'], 'source mismatch')
    for r in json.loads(owned['extra-sources.json'])['sources']:
        b = owned[r['local']]
        git = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        require(git == r['git_blob'] and digest(b) == r['sha256'], 'extra source mismatch')
    print(json.dumps({'result':'INTEGRITY_ONLY', 'review_payloads':len(owned),
                      'author_payloads':len(author), 'pinned_author_blobs':len(sources['pinned_blobs_verified']),
                      'mathematical_programs_run':False, 'writes':0}))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as e:
        raise SystemExit('VERIFICATION_REJECTED: ' + str(e))
