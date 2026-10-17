#!/usr/bin/env python3
"""Read-only exact-membership verification. Original code: MIT."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def read_json(data):
    return json.loads(data, object_pairs_hook=unique)


def canonical(name):
    p = PurePosixPath(name)
    require(isinstance(name, str) and name and not p.is_absolute()
            and name == str(p) and '..' not in p.parts and '.' not in p.parts
            and '\\' not in name, 'noncanonical inventory path')
    return name


def verify_inventory(root, manifest_name, anchor):
    require(root.is_dir() and not root.is_symlink(), 'invalid package root')
    mp = root / manifest_name
    require(mp.is_file() and not mp.is_symlink(), 'invalid manifest')
    data = mp.read_bytes()
    require(len(anchor) == 64 and sha(data) == anchor, 'external anchor mismatch')
    manifest = read_json(data)
    files = manifest['files']
    dirs = manifest['directories']
    require(isinstance(files, dict), 'files must be a mapping')
    require(len(dirs) == len(set(dirs)), 'duplicate directory')
    for name in list(files) + dirs:
        canonical(name)
    require(manifest_name not in files, 'manifest cannot inventory itself')
    found_files = set()
    found_dirs = set()
    for p in root.rglob('*'):
        require(not p.is_symlink(), 'symlink in package')
        name = p.relative_to(root).as_posix()
        if p.is_dir():
            found_dirs.add(name)
        else:
            require(p.is_file(), 'nonregular package entry')
            found_files.add(name)
    require(found_files == set(files) | {manifest_name}, 'file membership mismatch')
    require(found_dirs == set(dirs), 'directory membership mismatch')
    for name, rec in files.items():
        data = (root / name).read_bytes()
        require(len(data) == rec['bytes'] and sha(data) == rec['sha256'], 'changed file: ' + name)
    return manifest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    args = parser.parse_args()
    r = args.root
    own = verify_inventory(r, 'manifest.json', args.anchor)
    ids = read_json((r / 'input-identities.json').read_bytes())
    a = args.repo / canonical(ids['author_directory'])
    author = verify_inventory(a, ids['manifest'], ids['anchor'])
    for name, key in [('candidate.md', 'candidate_sha256'), ('scope.json', 'scope_sha256'),
                      ('reading-and-comparison.md', 'comparison_sha256'), ('verify_inventory.py', 'verifier_sha256')]:
        require(sha((a / name).read_bytes()) == ids[key], 'named author input mismatch')
    tree = read_json((r / canonical(ids['tree_snapshot'])).read_bytes())
    require(tree.get('truncated') is False, 'incomplete preprint tree')
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    for rec in ids['source_receipts']:
        data = (a / canonical(rec['path'])).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == rec['git_blob'] == blobs[rec['upstream_path']], 'source Git/tree mismatch')
        require(sha(data) == rec['sha256'] and len(data) == rec['bytes'], 'source bytes mismatch')
        require('/' + ids['pin'] + '/' in rec['url'], 'unpinned source URL')
    for rec in read_json((r / 'context-receipts.json').read_bytes()):
        data = (r / canonical(rec['snapshot'])).read_bytes()
        require(len(data) == rec['bytes'] and sha(data) == rec['sha256'], 'context snapshot mismatch')
    print(json.dumps({'status':'PASS_INTEGRITY_ONLY','review_payloads':len(own['files']),
                      'review_directories':len(own['directories']), 'author_payloads':len(author['files']),
                      'author_directories':len(author['directories']), 'pinned_blobs':len(ids['source_receipts']),
                      'verdict':'TECHNICAL','proof_certified':False,'counted':False}))

if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        sys.exit(1)
