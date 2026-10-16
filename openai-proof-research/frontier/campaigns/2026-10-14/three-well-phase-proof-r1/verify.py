#!/usr/bin/env python3
"""Read-only P3R review integrity check. Original code MIT; not a proof checker."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(path):
    need(isinstance(path, str) and path and '\\' not in path, 'unsafe path')
    p = PurePosixPath(path)
    need(not p.is_absolute() and p.as_posix() == path and
         all(x not in ('', '.', '..') for x in path.split('/')), 'noncanonical path')
    return path


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        need(key not in obj, 'duplicate JSON key')
        obj[key] = value
    return obj


def parse(data):
    return json.loads(data, object_pairs_hook=unique_object)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    need(re.fullmatch('[0-9a-f]{64}', args.anchor), 'anchor must be lowercase SHA256')
    own = Path(__file__).absolute().parent
    need(not own.is_symlink(), 'symlink package root')
    seal_path = own / 'seal.json'
    need(seal_path.is_file() and not seal_path.is_symlink(), 'bad seal file')
    seal_bytes = seal_path.read_bytes()
    # Authenticate externally anchored bytes before interpreting the envelope.
    need(sha(seal_bytes) == args.anchor, 'external seal anchor mismatch')
    seal = parse(seal_bytes)
    need(set(seal) == {'format', 'manifest_sha256', 'manifest_size'}, 'bad seal schema')
    need(seal['format'] == 'p3r-proof-review-seal-v1', 'bad seal format')
    manifest_path = own / 'manifest.json'
    need(manifest_path.is_file() and not manifest_path.is_symlink(), 'bad manifest file')
    manifest_bytes = manifest_path.read_bytes()
    need(len(manifest_bytes) == seal['manifest_size'] and
         sha(manifest_bytes) == seal['manifest_sha256'], 'manifest mismatch')
    manifest = parse(manifest_bytes)
    need(set(manifest) == {'format', 'files', 'directories'}, 'bad manifest schema')
    need(manifest['format'] == 'p3r-proof-review-manifest-v1', 'bad manifest format')
    entries = manifest['files']
    need(isinstance(entries, list), 'bad entries')
    expected_files = {'seal.json', 'manifest.json'}
    for entry in entries:
        need(set(entry) == {'path', 'size', 'sha256', 'role'}, 'bad file schema')
        path = safe(entry['path'])
        need(path not in expected_files, 'duplicate/reserved file path')
        expected_files.add(path)
        need(isinstance(entry['size'], int) and entry['size'] >= 0 and
             re.fullmatch('[0-9a-f]{64}', entry['sha256']), 'bad size/hash')
    expected_dirs = set()
    for path in manifest['directories']:
        path = safe(path)
        need(path not in expected_dirs and path not in expected_files, 'duplicate/colliding directory')
        expected_dirs.add(path)
    actual_files, actual_dirs = set(), set()
    for path in own.rglob('*'):
        relative = path.relative_to(own).as_posix()
        need(not path.is_symlink(), 'symlink: ' + relative)
        if path.is_dir():
            actual_dirs.add(relative)
        else:
            need(path.is_file(), 'nonregular member: ' + relative)
            actual_files.add(relative)
    need(actual_files == expected_files, 'file membership mismatch')
    need(actual_dirs == expected_dirs, 'directory membership mismatch')
    for entry in entries:
        data = (own / entry['path']).read_bytes()
        need(len(data) == entry['size'] and sha(data) == entry['sha256'],
             'file mismatch: ' + entry['path'])
    fixed = {
        'inputs/author/candidate.md': 'b03e265c57e60a198f7d1d3a63ac807ff4c8587b3fede3b4ef9c8c9664dbc4f4',
        'inputs/author/original-scope.md': '0a2aeb8c581e421037ad7c87936c2016495d5babb974ab64be0fa15a16dd66f5',
    }
    for path, digest in fixed.items():
        need(sha((own / path).read_bytes()) == digest, 'wrong reviewed input')
    auth = parse((own / 'inputs/author/source-authentication.json').read_bytes())
    verified = parse((own / 'source-verification.json').read_bytes())
    catalogue = parse((own / 'inputs/context/catalogue-extract.json').read_bytes())
    need(verified['commit'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'wrong commit')
    need(len(auth) == len(verified['files']) == len(catalogue['entries']) == 14,
         'wrong pinned inventory size')
    catalogue_map = {e['path'].removeprefix('preprints/'): e['sha'] for e in catalogue['entries']}
    need(len(catalogue_map) == 14 and catalogue['truncated'] is False, 'bad catalogue extract')
    verified_map = {e['path']: e for e in verified['files']}
    need(len(verified_map) == 14, 'duplicate verified source')
    for entry in auth:
        path = safe(entry['local'])
        need(path.startswith('inputs/pinned/'), 'source outside pinned inputs')
        data = (own / path).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        need(blob == entry['git_blob'] == catalogue_map[entry['upstream_path'].removeprefix('preprints/')],
             'source Git identity mismatch')
        observed = verified_map[entry['upstream_path']]
        need(sha(data) == entry['sha256'] == observed['sha256'] and
             len(data) == entry['size'] == observed['size'] and
             observed['git_blob'] == blob and observed['pinned_remote_equal'] is True,
             'source authentication record mismatch')
    before = parse((own / 'receipt-before.json').read_bytes())
    after = parse((own / 'receipt-after.json').read_bytes())
    need(set(before['files']) == set(after['files']), 'external receipt membership mismatch')
    for external, entry in before['files'].items():
        data = (own / safe(entry['snapshot'])).read_bytes()
        need(len(data) == entry['size'] and sha(data) == entry['sha256'], 'input snapshot changed')
        observed = after['files'][external]
        need(observed['snapshot_unchanged'] is True, 'after snapshot changed')
        need(observed['live_state'] in ('unchanged', 'changed', 'missing'), 'bad live observation')
    status = parse((own / 'status.json').read_bytes())
    need(status['mathematical_verdict'] == 'PASS_FULL_P3R' and
         status['required_repairs'] == [] and status['counted'] is False and
         status['author_handoff_reconciliation_required'] is True,
         'status scope mismatch')
    print(json.dumps({'integrity': 'PASS', 'payload_files': len(entries),
                      'all_files': len(actual_files), 'directories': len(actual_dirs),
                      'pinned_blobs': 14, 'mathematics_checked_by_this_program': False,
                      'live_inputs_unchanged': after['all_live_paths_unchanged']}, sort_keys=True))


if __name__ == '__main__':
    main()
