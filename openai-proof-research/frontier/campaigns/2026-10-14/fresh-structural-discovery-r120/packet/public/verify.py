#!/usr/bin/env python3
"""Read-only integrity verification, not a mathematical gate.
MIT; Myeongjin Kang. Adapted from structural r119 (r81/r80 ancestry).
Caller must supply detached FINAL and REPORT hashes and the complete tree.
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
TREEHASH = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def need(test, message):
    if not test:
        raise ValueError(message)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def read(path):
    st = path.lstat()
    need(stat.S_ISREG(st.st_mode) and st.st_nlink == 1,
         'nonregular, symlink or hardlinked file: ' + str(path))
    return path.read_bytes()


def safe(name):
    need(isinstance(name, str) and bool(name), 'invalid path')
    p = PurePosixPath(name)
    need(not p.is_absolute() and str(p) == name and '\\' not in name
         and all(x not in ('.', '..') for x in p.parts), 'unsafe path')


def scan(base):
    need(base.is_dir() and not base.is_symlink(), 'invalid packet root')
    files, directories = {}, []
    for here, ds, fs in os.walk(base, followlinks=False):
        for name in ds:
            p = Path(here) / name
            need(stat.S_ISDIR(p.lstat().st_mode), 'symlink/non-directory member')
            directories.append(p.relative_to(base).as_posix())
        for name in fs:
            p = Path(here) / name
            b = read(p)
            files[p.relative_to(base).as_posix()] = {'bytes': len(b), 'sha256': sha(b)}
    return files, sorted(directories)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--tree', required=True, type=Path)
    ap.add_argument('--finalhash', required=True)
    ap.add_argument('--reporthash', required=True)
    args = ap.parse_args()
    for h in (args.finalhash, args.reporthash):
        need(re.fullmatch('[0-9a-f]{64}', h), 'invalid detached hash')
    root = args.root.absolute()
    need(root.is_dir() and not root.is_symlink(), 'invalid root')
    packet = root / 'packet'
    fb = read(root / 'FINAL.json')
    need(sha(fb) == args.finalhash, 'FINAL external anchor mismatch')
    final = json.loads(fb)
    need(final.get('schema') == 'r120-detached-final-v1', 'FINAL schema')
    rb, mb = read(root / 'REPORT.md'), read(root / 'MANIFEST.json')
    need(sha(rb) == args.reporthash == final['report_sha256'], 'REPORT external anchor mismatch')
    need(sha(mb) == final['manifest_sha256'], 'manifest anchor mismatch')
    m = json.loads(mb)
    need(m.get('schema') == 'r120-exact-packet-v1' and m.get('pin') == PIN, 'manifest schema/pin')
    expected = {}
    for e in m['files']:
        safe(e['path'])
        need(e['path'] not in expected, 'duplicate manifest entry')
        expected[e['path']] = {'bytes': e['bytes'], 'sha256': e['sha256']}
    for d in m['directories']:
        safe(d)
    actual, directories = scan(packet)
    need(actual == expected and directories == m['directories'], 'exact packet bytes/membership mismatch')
    need(sha(read(packet / 'public/report.md')) == final['public_report_sha256'], 'public report mismatch')
    tb = read(args.tree)
    need(sha(tb) == TREEHASH, 'external complete-tree hash mismatch')
    tree = json.loads(tb)
    need(tree.get('truncated') is False and len(tree['tree']) == 13223
         and tree['sha'] == 'df0564b2deaab87e07854b6344d8c2f037682e77', 'complete-tree contract')
    td = {e['path']: e for e in tree['tree']}
    selection = json.loads(read(packet / 'private/canonical-selection.json'))
    need(selection['commit'] == PIN and selection['entries'] == 13223
         and selection['truncated'] is False and selection['tree_sha256'] == TREEHASH,
         'selection receipt contract')
    selected = {e['path']: e for e in selection['selected']}
    need(len(selected) == len(selection['selected']), 'duplicate canonical selection')
    sources = json.loads(read(packet / 'public/source-register.json'))
    need({e['path'] for e in sources} == set(selected) and len(sources) == len(selected), 'source selection mismatch')
    for e in sources:
        safe(e['local'])
        need(e['local'].startswith('private/upstream/'), 'source boundary')
        b = read(packet / e['local'])
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        c = td[e['path']]
        need(selected[e['path']] == c and c['type'] == 'blob', 'canonical tree entry mismatch')
        need(blob == c['sha'] == e['git_blob'] and len(b) == c['size'] == e['size']
             and sha(b) == e['sha256'], 'canonical blob mismatch')
        need(e['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + e['path'], 'unpinned source URL')
    primaries = json.loads(read(packet / 'public/primary-register.json'))
    for e in primaries:
        if not e['success']:
            continue
        for field in ('pdf', 'text'):
            safe(e[field])
            need(e[field].startswith('private/primary/'), 'primary boundary')
            need(sha(read(packet / e[field])) == e[field + '_sha256'], 'primary identity mismatch')
    histories = json.loads(read(packet / 'private/history-register.json'))
    for e in histories:
        safe(e['local'])
        need(e['local'].startswith('private/history/'), 'history boundary')
        b = read(packet / e['local'])
        need(len(b) == e['bytes'] and sha(b) == e['sha256'], 'history identity mismatch')
    print(json.dumps({'result': 'INTEGRITY_ONLY_OK', 'files': len(actual),
                      'canonical_blobs': len(sources), 'primary_pairs': sum(e['success'] for e in primaries),
                      'history_copies': len(histories), 'mathematical_gate': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as exc:
        print('INTEGRITY_REJECTED: ' + str(exc), file=sys.stderr)
        sys.exit(1)
