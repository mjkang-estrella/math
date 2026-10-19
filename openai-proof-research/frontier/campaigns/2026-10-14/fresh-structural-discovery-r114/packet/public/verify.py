#!/usr/bin/env python3
"""Read-only byte/provenance verification; a DETACHED final manifest hash is mandatory.
Trust this script and Python separately. This is never a mathematical gate.
"""
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

def need(test, why):
    if not test:
        raise ValueError(why)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result

def parse(data):
    return json.loads(data, object_pairs_hook=unique)

def safe(name):
    need(isinstance(name, str) and name and '\\' not in name, 'invalid path')
    p = PurePosixPath(name)
    need(not p.is_absolute() and str(p) == name and all(x not in ('.', '..') for x in p.parts), 'noncanonical path')
    return name

def inventory(root):
    root = Path(os.path.abspath(root))
    for p in [root, *root.parents]:
        need(stat.S_ISDIR(p.lstat().st_mode), 'root or ancestor is not a real directory')
    entries = []
    for here, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            p = Path(here) / name
            rel = safe(p.relative_to(root).as_posix())
            info = p.lstat()
            if stat.S_ISDIR(info.st_mode):
                entries.append(dict(path=rel, type='directory', size=0, sha256=None))
            else:
                need(stat.S_ISREG(info.st_mode), 'nonregular entry: ' + rel)
                need(info.st_nlink == 1, 'hardlink: ' + rel)
                entries.append(dict(path=rel, type='file', size=info.st_size, sha256=sha(p.read_bytes())))
    return sorted(entries, key=lambda x: x['path'])

def verify(root, anchor):
    need(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'malformed detached anchor')
    inv = inventory(root)
    items = {e['path']: e for e in inv}
    need('manifest.json' in items and items['manifest.json']['type'] == 'file', 'missing manifest')
    need(items['manifest.json']['sha256'] == anchor, 'detached manifest hash mismatch')
    manifest = parse((root / 'manifest.json').read_bytes())
    need(set(manifest) == {'schema', 'pin', 'root_type', 'directory_size_convention', 'entries'}, 'manifest keys')
    need(manifest['schema'] == 'r114-exact-inventory-v1' and manifest['pin'] == PIN, 'schema or pin')
    need(manifest['root_type'] == 'directory' and manifest['directory_size_convention'] == 'zero logical payload bytes; child membership exact', 'directory convention')
    desired = manifest['entries']
    need(isinstance(desired, list), 'inventory list')
    names = []
    for row in desired:
        need(set(row) == {'path', 'type', 'size', 'sha256'}, 'inventory entry keys')
        name = safe(row['path']); names.append(name)
        need(name != 'manifest.json', 'recursive manifest')
        if row['type'] == 'file':
            need(type(row['size']) is int and row['size'] >= 0 and isinstance(row['sha256'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256']), 'file size or digest')
        else:
            need(row['type'] == 'directory' and row['size'] == 0 and row['sha256'] is None, 'directory record')
    need(names == sorted(set(names)), 'duplicate or unsorted inventory')
    need([e for e in inv if e['path'] != 'manifest.json'] == desired, 'exact inventory mismatch')
    def read(name):
        need(name in items and items[name]['type'] == 'file', 'unlisted receipt')
        return parse((root / name).read_bytes())
    treepath = 'private/context/preprints-tree.json'
    need(items[treepath]['sha256'] == TREE_HASH, 'canonical tree identity')
    upstream = read('private/context/upstream.json')
    need(upstream['repository'] == 'https://github.com/openai/math' and upstream['commit'] == PIN, 'upstream repository or commit')
    tree = read(treepath)
    need(tree['truncated'] is False and len(tree['tree']) == 13223, 'incomplete tree')
    canonical = {x['path']: x for x in tree['tree']}
    need(len(canonical) == 13223, 'duplicate tree paths')
    source = read('private/upstream-receipts.json')
    seen = set(); locals_seen = set()
    for rec in source:
        path, local = safe(rec['path']), safe(rec['local'])
        need(path not in seen, 'duplicate source receipt'); seen.add(path)
        need(local == 'private/upstream/' + path and local in items, 'source local identity')
        locals_seen.add(local)
        ent = canonical[path]; data = (root / local).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode('ascii') + b'\0' + data).hexdigest()
        need(ent['type'] == 'blob' and ent['sha'] == rec['git_blob'] == blob, 'Git blob identity')
        need(ent['size'] == rec['size'] == len(data) and sha(data) == rec['sha256'], 'source size or sha256')
        need(rec['raw_url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + path, 'pinned raw identity')
    need(locals_seen == {p for p, e in items.items() if p.startswith('private/upstream/') and e['type'] == 'file'}, 'unreceipted source body')
    for family in read('private/context/family-map.json').values():
        for ent in family['files']:
            need(ent == canonical[ent['path']], 'family-map canonical mismatch')
    primaries = read('private/primary-receipts.json'); seen_names = set(); primaryfiles = set()
    for rec in primaries:
        need(rec['name'] not in seen_names, 'duplicate primary'); seen_names.add(rec['name'])
        need(isinstance(rec['version'], str) and rec['version'], 'missing primary version')
        need(rec['url'].startswith('https://') and rec['retrieved_utc'], 'primary retrieval identity')
        if rec['success'] is True:
            need(rec['resolved_url'].startswith('https://') and len(rec['files']) == 2, 'primary body pair')
            for f in rec['files']:
                local = safe(f['local']); need(local.startswith('private/primary/') and local in items, 'primary local')
                need(items[local]['size'] == f['size'] and items[local]['sha256'] == f['sha256'], 'primary bytes')
                primaryfiles.add(local)
        else:
            need(rec['success'] is False and rec['error'], 'failed retrieval record')
    need(primaryfiles == {p for p, e in items.items() if p.startswith('private/primary/') and e['type'] == 'file'}, 'unreceipted primary body')
    for rec in read('private/context/history-receipts.json'):
        local = safe(rec['local'])
        need(items[local]['size'] == rec['size'] and items[local]['sha256'] == rec['sha256'], 'history copy identity')
    return dict(status='integrity_only', manifest_sha256=anchor, files=sum(e['type']=='file' for e in desired), directories=sum(e['type']=='directory' for e in desired), upstream_blobs=len(source), primary_versions=len(primaries))

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('packet', type=Path)
    ap.add_argument('--expected-manifest-sha256', required=True)
    args = ap.parse_args()
    try:
        print(json.dumps(verify(args.packet, args.expected_manifest_sha256), sort_keys=True, indent=2))
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print('INTEGRITY FAILURE: ' + str(exc), file=sys.stderr)
        sys.exit(1)
