#!/usr/bin/env python3
"""Read-only byte/provenance verifier. Detached anchors are mandatory; no math gate."""
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
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def need(condition, reason):
    if not condition:
        raise ValueError(reason)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def regular(path):
    s = path.lstat()
    need(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'nonregular-or-linked-file:' + str(path))
    return path.read_bytes()

def clean(name):
    need(isinstance(name, str) and name and '\\' not in name, 'unsafe-path')
    q = PurePosixPath(name)
    need(not q.is_absolute() and all(x not in ('', '.', '..') for x in name.split('/')),
         'unsafe-path')
    need(str(q) == name, 'unsafe-path')
    return name

def jread(path):
    return json.loads(regular(path))

def inventory(packet):
    need(stat.S_ISDIR(packet.lstat().st_mode), 'nonregular-packet-root')
    files, dirs = {}, []
    for base, dn, fn in os.walk(packet, followlinks=False):
        base = Path(base)
        for name in dn:
            child = base / name
            need(stat.S_ISDIR(child.lstat().st_mode), 'nonregular-directory:' + str(child))
            dirs.append(child.relative_to(packet).as_posix())
        for name in fn:
            child = base / name
            data = regular(child)
            files[child.relative_to(packet).as_posix()] = {'bytes': len(data), 'sha256': digest(data)}
    return dict(sorted(files.items())), sorted(dirs)

def verify(root, tree_path, finalhash, reporthash):
    need(re.fullmatch('[0-9a-f]{64}', finalhash) is not None, 'invalid-detached-finalhash')
    need(re.fullmatch('[0-9a-f]{64}', reporthash) is not None, 'invalid-detached-reporthash')
    need(stat.S_ISDIR(root.lstat().st_mode), 'nonregular-root')
    finalbytes = regular(root / 'FINAL.json')
    need(digest(finalbytes) == finalhash, 'detached-finalhash-mismatch')
    final = json.loads(finalbytes)
    need(set(final) == {'schema','pin','status','manifest_sha256','report_sha256','packet_report_sha256'}, 'final-schema')
    need(final['schema'] == 1 and final['pin'] == PIN and final['status'] == 'PREFREEZE_NO_NOMINEE', 'final-contract')
    need(digest(regular(root / 'REPORT.md')) == reporthash == final['report_sha256'], 'detached-reporthash-mismatch')
    mbytes = regular(root / 'MANIFEST.json')
    need(digest(mbytes) == final['manifest_sha256'], 'manifest-hash-mismatch')
    manifest = json.loads(mbytes)
    need(set(manifest) == {'schema','pin','files','directories'} and manifest['schema'] == 1 and manifest['pin'] == PIN, 'manifest-schema')
    for name in manifest['files']:
        clean(name)
    for name in manifest['directories']:
        clean(name)
    packet = root / 'packet'
    files, dirs = inventory(packet)
    need(set(files) == set(manifest['files']), 'packet-file-inventory-mismatch')
    need(dirs == manifest['directories'], 'packet-directory-inventory-mismatch')
    need(files == manifest['files'], 'packet-payload-mismatch')
    need(files['public/report.md']['sha256'] == final['packet_report_sha256'], 'packet-report-binding')
    tb = regular(tree_path)
    need(digest(tb) == TREE_SHA, 'canonical-tree-hash-mismatch')
    tree = json.loads(tb)
    need(tree['truncated'] is False and len(tree['tree']) == 13223, 'canonical-tree-shape')
    idx = {e['path']: e for e in tree['tree']}
    need(len(idx) == 13223, 'canonical-tree-duplicates')
    types = {t: sum(e['type'] == t for e in tree['tree']) for t in ['blob','tree']}
    need(types == {'blob':10373,'tree':2850}, 'canonical-tree-types')
    select = jread(packet/'public/canonical-selection.json')
    need(select['pin'] == PIN and select['tree_sha256'] == TREE_SHA and select['entries'] == 13223
         and select['truncated'] is False and select['types'] == types, 'selection-tree-binding')
    src = jread(packet/'public/source-register.json')
    need(len(src) == select['retained_count'] == 20, 'canonical-source-count')
    need(len({e['path'] for e in src}) == len(src), 'canonical-source-duplicates')
    need(select['selected_entries'] == [idx[e['path']] for e in src], 'selected-entry-binding')
    for e in src:
        name = clean(e['local'])
        need(name == 'private/upstream/' + e['path'], 'canonical-local-path')
        need(e['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + e['path'], 'canonical-url')
        data = regular(packet/name)
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        need(idx[e['path']]['type'] == 'blob' and blob == idx[e['path']]['sha'] == e['git_blob'], 'canonical-git-blob')
        need(digest(data) == e['sha256'] and len(data) == e['bytes'], 'canonical-sha256')
    need({x for x in files if x.startswith('private/upstream/')} == {e['local'] for e in src}, 'unregistered-upstream')
    acquisitions = jread(packet/'private/acquisition-register.json')
    need(len(acquisitions) == select['acquired_count'] == 151, 'acquisition-count')
    need(len({e['path'] for e in acquisitions}) == 151, 'acquisition-duplicates')
    for e in acquisitions:
        need(idx[e['path']]['type'] == 'blob' and e['git_blob'] == idx[e['path']]['sha'], 'acquisition-tree-binding')
        need(e['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + e['path'], 'acquisition-url')
        need(e['retained'] == (e['path'] in {x['path'] for x in src}), 'acquisition-retention')
    prim = jread(packet/'public/primary-register.json')
    success = [e for e in prim if e['status'] == 'success']
    failed = [e for e in prim if e['status'] == 'failure']
    need(len(success) == 6 and len(failed) == 2, 'primary-count')
    expected_primary = set()
    for e in success:
        for kind in ['pdf','text']:
            name = clean(e[kind]); need(name.startswith('private/primary/'), 'primary-path')
            expected_primary.add(name)
            need(digest(regular(packet/name)) == e[kind+'_sha256'], 'primary-representation')
        need(len(regular(packet/e['text']).decode().split('\n')) == e['text_lines'], 'primary-line-count')
    need(expected_primary == {x for x in files if x.startswith('private/primary/')}, 'unregistered-primary')
    for e in jread(packet/'public/history-register.json'):
        name = clean(e['local']); need(name.startswith('private/history/'), 'history-path')
        data = regular(packet/name)
        need(digest(data) == e['sha256'] and len(data) == e['bytes'], 'history-body-binding')
    return {'status':'INTEGRITY_ONLY_OK','payload_files':len(files),'directories':len(dirs),
            'canonical_blobs':len(src),'primary_pairs':len(success),'failed_primary_versions':len(failed),
            'final_sha256':finalhash,'report_sha256':reporthash}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--tree', required=True, type=Path)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    a = ap.parse_args()
    try:
        print(json.dumps(verify(a.root, a.tree, a.finalhash, a.reporthash), sort_keys=True))
    except (ValueError, KeyError, TypeError, OSError) as e:
        print('REJECT: ' + str(e), file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
