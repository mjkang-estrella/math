#!/usr/bin/env python3
"""Read-only exact-inventory verifier. The expected manifest hash is external."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def inventory(root):
    require(root.is_dir() and not root.is_symlink(), 'packet root must be a real directory')
    out = []
    for base, dirs, files in os.walk(root, followlinks=False):
        for name in sorted(dirs + files):
            p = Path(base) / name
            rel = p.relative_to(root).as_posix()
            mode = p.lstat().st_mode
            require(not stat.S_ISLNK(mode), 'symlink forbidden: ' + rel)
            require(stat.S_ISDIR(mode) or stat.S_ISREG(mode), 'special file forbidden: ' + rel)
            if rel == 'manifest.json':
                require(stat.S_ISREG(mode), 'manifest must be regular')
                continue
            if stat.S_ISDIR(mode):
                out.append({'path': rel, 'type': 'directory'})
            else:
                data = p.read_bytes()
                out.append({'path': rel, 'type': 'file', 'bytes': len(data), 'sha256': sha(data)})
    return sorted(out, key=lambda x: x['path'])

def verify(root, expected):
    require(re.fullmatch(r'[0-9a-f]{64}', expected) is not None, 'expected hash must be 64 lowercase hex digits')
    require(root.is_dir() and not root.is_symlink(), 'packet root must be a real directory')
    mf = root / 'manifest.json'
    require(mf.is_file() and not mf.is_symlink(), 'manifest must be a regular non-symlink file')
    raw = mf.read_bytes()
    require(sha(raw) == expected, 'detached manifest anchor mismatch')
    doc = json.loads(raw)
    require(set(doc) == {'schema', 'pin', 'status', 'entries'}, 'manifest fields mismatch')
    require(doc['schema'] == 'r115-exact-packet-v1' and doc['pin'] == PIN, 'manifest identity mismatch')
    require(doc['status'] == 'prefreeze-no-nominee', 'manifest status mismatch')
    entries = doc['entries']
    require(isinstance(entries, list), 'entries must be a list')
    names = [e['path'] for e in entries]
    require(names == sorted(set(names)), 'manifest paths must be sorted and unique')
    for e in entries:
        rel = PurePosixPath(e['path'])
        require(not rel.is_absolute() and '..' not in rel.parts and str(rel) == e['path'], 'unsafe path')
        require(e['path'] != 'manifest.json', 'manifest must not anchor itself')
        fields = {'path', 'type'} if e['type'] == 'directory' else {'path', 'type', 'bytes', 'sha256'}
        require(set(e) == fields and e['type'] in ('directory', 'file'), 'entry schema mismatch')
    actual = inventory(root)
    require([e['path'] for e in actual] == names, 'exact inventory mismatch')
    require(actual == entries, 'payload content or type mismatch')
    tree = json.loads((root/'private/complete-tree-receipt.json').read_text())
    require(tree['pin'] == PIN and tree['sha256'] == TREE_SHA256 and tree['entries'] == 13223 and tree['truncated'] is False, 'complete tree receipt mismatch')
    nav = json.loads((root/'private/navigation.json').read_text())
    blobs = {r['path']: r for r in nav['operative_complete_tree_blobs']}
    source = json.loads((root/'private/upstream-receipts.json').read_text())
    kept = set()
    for r in source:
        require(r['raw_url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + r['path'], 'source URL/pin mismatch')
        require(r['local'] == 'private/upstream/' + r['path'], 'source local path mismatch')
        p = root/r['local']
        if not r['retained']:
            require(not p.exists(), 'unretained source unexpectedly present')
            continue
        data = p.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == r['git_blob'] and sha(data) == r['sha256'] and len(data) == r['size'], 'source identity mismatch')
        require(r['path'] in blobs and blobs[r['path']]['git_blob'] == blob and blobs[r['path']]['size'] == len(data), 'tree blob receipt mismatch')
        kept.add(r['path'])
    require(kept == set(blobs), 'retained source set mismatch')
    primary = json.loads((root/'private/primary-receipts.json').read_text())
    for r in primary:
        if 'failure' in r:
            continue
        for kind, ext in [('pdf', 'pdf'), ('text', 'txt')]:
            p = root/'private/primary'/(r['name'] + '.' + ext)
            if r[kind + '_retained']:
                data = p.read_bytes()
                require(sha(data) == r[kind + '_sha256'] and len(data) == r[kind + '_size'], 'primary identity mismatch')
            else:
                require(not p.exists(), 'unretained primary unexpectedly present')
    return {'integrity': 'verified', 'mathematical_gate': False, 'manifest_sha256': expected,
            'report_sha256': sha((root/'public/report.md').read_bytes()),
            'files': sum(e['type'] == 'file' for e in entries), 'directories': sum(e['type'] == 'directory' for e in entries),
            'retained_upstream_blobs': len(kept)}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--expected-manifest-sha256', required=True)
    args = parser.parse_args()
    try:
        result = verify(args.packet, args.expected_manifest_sha256)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print('REJECT: ' + str(exc), file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0

if __name__ == '__main__':
    sys.exit(main())
