#!/usr/bin/env python3
"""Read-only exact inventory/provenance check; requires detached caller anchors.
This is not a mathematical, contribution or acceptance gate. Authenticate this
verifier independently. An attacker replacing code and anchors can defeat any
self-contained integrity scheme. No network or repository reads are performed.
"""
import argparse
import hashlib
import json
import re
import stat
from pathlib import Path, PurePosixPath

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pairs(items):
    result = {}
    for key, val in items:
        require(key not in result, 'duplicate JSON key')
        result[key] = val
    return result


def read_json(path):
    return json.loads(path.read_bytes(), object_pairs_hook=pairs)


def clean(value):
    require(isinstance(value, str) and value, 'nonstring/empty path')
    p = PurePosixPath(value)
    require(not p.is_absolute() and str(p) == value and
            all(x not in ('.', '..') for x in p.parts), 'unsafe path')
    return value


def inventory(packet):
    require(packet.is_dir() and not packet.is_symlink(), 'invalid packet root')
    files, dirs = {}, []
    for p in sorted(packet.rglob('*')):
        rel = clean(p.relative_to(packet).as_posix())
        st = p.lstat()
        require(not stat.S_ISLNK(st.st_mode), 'symlink: ' + rel)
        if stat.S_ISDIR(st.st_mode):
            dirs.append(rel)
        else:
            require(stat.S_ISREG(st.st_mode) and st.st_nlink == 1,
                    'special/hardlinked file: ' + rel)
            b = p.read_bytes()
            files[rel] = {'bytes': len(b), 'sha256': sha(b)}
    return files, dirs


def verify(packet, finalhash, reporthash):
    for value in (finalhash, reporthash):
        require(re.fullmatch('[0-9a-f]{64}', value) is not None, 'invalid detached hash')
    files, dirs = inventory(packet)
    mb = (packet / 'MANIFEST.json').read_bytes()
    require(sha(mb) == finalhash, 'detached finalhash mismatch')
    m = read_json(packet / 'MANIFEST.json')
    require(set(m) == {'schema', 'pin', 'files', 'directories'}, 'manifest fields')
    require(m['schema'] == 1 and m['pin'] == PIN, 'manifest schema/pin')
    require('MANIFEST.json' not in m['files'], 'self-indexed manifest')
    for path in m['files']:
        clean(path)
    for path in m['directories']:
        clean(path)
    del files['MANIFEST.json']
    require(files == m['files'], 'exact file inventory/hash mismatch')
    require(dirs == m['directories'], 'exact directory inventory mismatch')
    require(sha((packet / 'public/report.md').read_bytes()) == reporthash,
            'detached reporthash mismatch')
    tree = read_json(packet / 'private/tree-receipt.json')
    require(tree['entries'] == 13223 and tree['truncated'] is False and
            tree['all_entries_parsed'] is True and tree['pin'] == PIN and
            tree['sha256'] == TREE, 'complete-tree receipt')
    es = read_json(packet / 'private/selected-tree.json')
    selected = {e['path']: e for e in es}
    require(len(selected) == len(es), 'duplicate selected entry')
    rs = read_json(packet / 'private/upstream-receipts.json')
    require(len(rs) == len(es), 'source receipt/entry count')
    seen, locals_seen = set(), set()
    for r in rs:
        path, local = clean(r['path']), clean(r['local'])
        require(path not in seen and local not in locals_seen, 'duplicate source receipt')
        seen.add(path); locals_seen.add(local)
        require(local.startswith('private/upstream/'), 'source outside private upstream')
        b = (packet / local).read_bytes()
        require(len(b) == r['bytes'] and sha(b) == r['sha256'], 'source SHA/size')
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        require(blob == r['git_blob'] == selected[path]['sha'] and
                selected[path]['type'] == 'blob', 'source Git blob')
        require(r['raw_url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + path,
                'source pinned URL')
    prim = read_json(packet / 'private/primary-receipts.json')
    success, failed = 0, 0
    for r in prim:
        if r['status'] == 'failure':
            require(bool(r.get('error')), 'missing acquisition failure')
            failed += 1
            continue
        require(r['status'] == 'success', 'unknown primary status')
        stem = clean(r['stem'])
        require('/' not in stem, 'primary stem path')
        pdf = (packet / 'private/primary' / (stem + '.pdf')).read_bytes()
        txt = (packet / 'private/primary' / (stem + '.txt')).read_bytes()
        require(len(pdf) == r['bytes'] and sha(pdf) == r['pdf_sha256'], 'primary PDF')
        require(sha(txt) == r['text_sha256'], 'primary text')
        success += 1
    register = read_json(packet / 'public/source-register.json')
    require(register == {'pin': PIN, 'complete_tree': tree, 'upstream': rs, 'primary': prim},
            'public/private provenance mismatch')
    return {'integrity': 'verified', 'finalhash': finalhash, 'reporthash': reporthash,
            'payload_files': len(files), 'directories': len(dirs), 'pinned_blobs': len(rs),
            'primary_successes': success, 'primary_failures_recorded': failed,
            'full_tree_replayed': False,
            'limit': 'Selected tree entries and complete-tree receipt authenticated; no full tree copy, network, or live history replay.',
            'mathematical_gate': False, 'contribution_gate': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', type=Path, required=True)
    p.add_argument('--finalhash', required=True)
    p.add_argument('--reporthash', required=True)
    a = p.parse_args()
    try:
        result = verify(a.packet, a.finalhash, a.reporthash)
    except (OSError, ValueError, KeyError, TypeError) as e:
        p.exit(1, 'INTEGRITY REJECTED: ' + str(e) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
