#!/usr/bin/env python3
"""Read-only byte/provenance verifier. No mathematical certification."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_HASH = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result

def decode(data):
    return json.loads(data, object_pairs_hook=unique_object)

def safe_name(name):
    require(isinstance(name, str) and name != '', 'invalid path')
    q = PurePosixPath(name)
    require(not q.is_absolute() and '..' not in q.parts and '.' not in q.parts
            and str(q) == name and '\\' not in name, 'unsafe path')
    return name

def verify(root, finalhash):
    require(re.fullmatch('[0-9a-f]{64}', finalhash) is not None,
            'finalhash must be detached lowercase SHA256')
    root = Path(os.path.abspath(root))
    for part in reversed((root, *root.parents)):
        require(not stat.S_ISLNK(part.lstat().st_mode), 'symlink ancestor')
    require(root.is_dir(), 'packet is not directory')
    paths, directories = {}, []
    for base, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            p = Path(base) / name
            info = p.lstat()
            rel = p.relative_to(root).as_posix()
            safe_name(rel)
            require(not stat.S_ISLNK(info.st_mode), 'symlink payload')
            if stat.S_ISDIR(info.st_mode):
                directories.append(rel)
            else:
                require(stat.S_ISREG(info.st_mode), 'nonregular payload')
                require(info.st_nlink == 1, 'hardlinked payload')
                paths[rel] = p
    require('manifest.json' in paths, 'missing manifest')
    manifest_bytes = paths['manifest.json'].read_bytes()
    require(digest(manifest_bytes) == finalhash, 'detached manifest hash mismatch')
    m = decode(manifest_bytes)
    require(set(m) == {'schema', 'pin', 'directories', 'files'}, 'manifest schema keys')
    require(m['schema'] == 'r75-exact-packet-v1', 'manifest schema')
    require(m['pin'] == PIN, 'wrong upstream pin')
    expected = {}
    for row in m['files']:
        require(set(row) == {'path', 'bytes', 'sha256'}, 'file entry schema')
        name = safe_name(row['path'])
        require(name != 'manifest.json' and name not in expected, 'duplicate or self manifest')
        require(type(row['bytes']) is int and row['bytes'] >= 0, 'invalid length')
        require(re.fullmatch('[0-9a-f]{64}', row['sha256']) is not None, 'invalid digest')
        expected[name] = row
    require(list(expected) == sorted(expected), 'unsorted manifest')
    require(set(paths) == set(expected) | {'manifest.json'}, 'file inventory mismatch')
    require(m['directories'] == sorted(set(m['directories'])), 'directory schema')
    for name in m['directories']:
        safe_name(name)
    require(sorted(directories) == m['directories'], 'directory inventory mismatch')
    blobs = {}
    for name, row in expected.items():
        data = paths[name].read_bytes()
        require(len(data) == row['bytes'] and digest(data) == row['sha256'],
                'payload hash mismatch: ' + name)
        blobs[name] = data
    def payload(name):
        safe_name(name)
        require(name in blobs, 'receipt points outside manifest')
        return blobs[name]
    canonical = decode(payload('private/canonical-selection.json'))
    require(canonical['pin'] == PIN and canonical['truncated'] is False
            and canonical['complete_tree_entries'] == 13223
            and canonical['complete_tree_sha256'] == TREE_HASH, 'canonical tree identity')
    selected = {}
    for entry in canonical['selected_entries']:
        require(entry['path'] not in selected, 'duplicate canonical path')
        selected[entry['path']] = entry
    sources = decode(payload('private/source-provenance.json'))
    seen = set()
    for record in sources:
        name = record['path']
        require(name not in seen, 'duplicate source receipt')
        seen.add(name)
        data = payload(name)
        entry = selected.get(record['upstream_path'])
        require(entry is not None and entry['type'] == 'blob', 'source absent from selected tree')
        git = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(git == record['git_blob'] == entry['sha'], 'Git blob mismatch')
        require(len(data) == record['bytes'] == entry['size']
                and digest(data) == record['sha256'], 'source receipt mismatch')
        require(record['raw_url'] == 'https://raw.githubusercontent.com/openai/math/'
                + PIN + '/' + record['upstream_path'], 'unpinned source URL')
    require(len(sources) == 41 and len(selected) == 41, 'source receipt count')
    require(seen == {n for n in blobs if n.startswith('private/upstream/')}, 'source coverage')
    primary = decode(payload('private/primary-provenance.json'))
    primary_names = set()
    for record in primary:
        require(record['status'] in {'success', 'copied-existing-primary'}, 'primary status')
        require(record['url'].startswith('https://'), 'primary URL')
        for kind in ('pdf', 'text'):
            name = record[kind]
            require(name not in primary_names, 'duplicate primary receipt')
            primary_names.add(name)
            require(digest(payload(name)) == record[kind + '_sha256'], 'primary receipt mismatch')
    require(len(primary) == 6, 'primary count')
    require(primary_names == {n for n in blobs if n.startswith('private/primary/')}, 'primary coverage')
    selection = decode(payload('public/selection-status.json'))
    require(selection['frozen_target'] is None and selection['nominee'] is None
            and selection['count_or_gate_assignment'] is None, 'screen status mismatch')
    print(json.dumps({'integrity': 'verified', 'manifest_sha256': finalhash,
                      'payload_files': len(expected), 'source_bodies': len(sources),
                      'primary_versions': len(primary), 'mathematical_gate': False}, sort_keys=True))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', required=True)
    parser.add_argument('--finalhash', required=True,
                        help='detached manifest SHA256 supplied outside the packet')
    args = parser.parse_args()
    try:
        verify(args.packet, args.finalhash)
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as error:
        print('REJECTED: ' + str(error), file=sys.stderr)
        sys.exit(1)
