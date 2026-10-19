#!/usr/bin/env python3
"""Read-only artifact/provenance verification; never a mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

sys.dont_write_bytecode = True
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX = 'https://raw.githubusercontent.com/openai/math/' + PIN + '/'


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    out = {}
    for key, val in pairs:
        require(key not in out, 'duplicate JSON key')
        out[key] = val
    return out


def read_json(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique)


def safe(path):
    p = PurePosixPath(path)
    return (isinstance(path, str) and bool(path) and not p.is_absolute()
            and '..' not in p.parts and p.as_posix() == path
            and '\\' not in path and '\x00' not in path and path != '.')


def inspect(root):
    require(root.is_dir() and not root.is_symlink(), 'invalid packet root')
    files, dirs = set(), set()
    for parent, dnames, fnames in os.walk(root, followlinks=False):
        for name in dnames + fnames:
            p = Path(parent) / name
            s = p.lstat()
            rel = p.relative_to(root).as_posix()
            require(not stat.S_ISLNK(s.st_mode), 'symlink: ' + rel)
            if stat.S_ISDIR(s.st_mode):
                dirs.add(rel)
            else:
                require(stat.S_ISREG(s.st_mode), 'nonregular file: ' + rel)
                files.add(rel)
    return files, dirs


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--finalhash', required=True,
                    help='DETACHED SHA256 supplied independently by the caller')
    ap.add_argument('--tree', type=Path,
                    help='optional external complete canonical preprints-tree.json')
    a = ap.parse_args()
    require(re.fullmatch('[0-9a-f]{64}', a.finalhash) is not None,
            'malformed detached finalhash')
    files, dirs = inspect(a.root)
    require('manifest.json' in files, 'missing manifest')
    mbytes = (a.root / 'manifest.json').read_bytes()
    require(digest(mbytes) == a.finalhash, 'detached finalhash mismatch')
    m = json.loads(mbytes, object_pairs_hook=unique)
    require(set(m) == {'schema', 'pin', 'files', 'directories'}, 'manifest schema')
    require(m['schema'] == 1 and m['pin'] == PIN, 'manifest version or pin')
    require(isinstance(m['files'], dict), 'manifest file mapping')
    require(all(safe(p) for p in m['files']), 'unsafe file path')
    require(all(safe(p) for p in m['directories']), 'unsafe directory path')
    require(len(m['directories']) == len(set(m['directories'])), 'duplicate directory')
    require(files == set(m['files']) | {'manifest.json'}, 'file membership mismatch')
    require(dirs == set(m['directories']), 'directory membership mismatch')
    for rel, expected in m['files'].items():
        require(set(expected) == {'sha256', 'bytes'}, 'file record schema')
        data = (a.root / rel).read_bytes()
        require(len(data) == expected['bytes'] and digest(data) == expected['sha256'],
                'payload mismatch: ' + rel)
    records = read_json(a.root / 'private/upstream-manifest.json')
    selection = read_json(a.root / 'private/selected-tree-entries.json')
    canonical = {e['path']: e for e in selection['entries']}
    require(len(canonical) == len(records) == 20, 'source inventory size')
    require(selection['commit'] == PIN and selection['complete_entry_count'] == 13223
            and selection['complete_truncated'] is False, 'source tree metadata')
    require({r['path'] for r in records} == set(canonical), 'source membership')
    for rec in records:
        require(safe(rec['local']) and rec['local'].startswith('private/upstream/'),
                'unsafe source body path')
        require(rec['raw_url'] == PREFIX + rec['path'], 'source URL mismatch')
        data = (a.root / rec['local']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == rec['git_blob'] == canonical[rec['path']]['sha'],
                'source Git blob mismatch')
        require(len(data) == rec['bytes'] and digest(data) == rec['sha256'],
                'source SHA256 mismatch')
        require(len(data) == canonical[rec['path']]['size'], 'canonical source size')
    if a.tree is not None:
        tbytes = a.tree.read_bytes()
        require(digest(tbytes) == selection['complete_tree_sha256'], 'external tree hash')
        tree = json.loads(tbytes, object_pairs_hook=unique)
        require(tree['truncated'] is False and len(tree['tree']) == 13223,
                'external tree incomplete')
        all_entries = {e['path']: e for e in tree['tree']}
        require(len(all_entries) == 13223, 'external tree duplicate paths')
        require(all(all_entries.get(p) == e for p, e in canonical.items()),
                'external tree entry mismatch')
    for rec in read_json(a.root / 'private/primary/manifest.json'):
        require(rec['status'] == 'success', 'unresolved primary retrieval')
        for suffix, key in [('.pdf', 'sha256'), ('.txt', 'text_sha256')]:
            p = a.root / 'private/primary' / (rec['name'] + suffix)
            require(digest(p.read_bytes()) == rec[key], 'primary body mismatch')
    status = read_json(a.root / 'public/status.json')
    require(status['nominee'] is None and status['frozen_target'] is None
            and status['count_assignment'] is None, 'screen disposition mismatch')
    print(json.dumps({'artifact_integrity': 'verified', 'payload_files': len(m['files']),
                      'upstream_blobs': len(records), 'external_tree_checked': a.tree is not None,
                      'mathematical_gate': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print('REJECT: ' + str(exc), file=sys.stderr)
        sys.exit(1)
