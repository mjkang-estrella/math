#!/usr/bin/env python3
"""MIT. Read-only artifact verifier; no analytic or contribution verdict."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def guard(event, args):
    if event == 'open':
        mode = args[1] or ''
        flags = args[2] if len(args) > 2 else 0
        if any(c in str(mode) for c in 'wax+') or (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
            raise RuntimeError('read-only: writable open denied')
    if event in {'os.remove', 'os.rename', 'os.mkdir', 'os.rmdir', 'os.chmod', 'os.chown', 'os.utime', 'os.link', 'os.symlink', 'os.truncate', 'subprocess.Popen', 'os.system', 'socket.connect', 'socket.bind'}:
        raise RuntimeError('read-only: ' + event + ' denied')


sys.addaudithook(guard)
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
AUTHOR_FINAL = '8419adc4398f7b682aa3ee5f5e08397d90e2815d2869fffde4bd6f64ee4de28d'
AUTHOR_REPORT = '26aaf530d6ce6d6fc20e8265937fe416945eb968efe451bf42e95b1491a77587'
SCOPE = 'ec4ebab8030a197d780522b2b64d841b3a06de167a32945832361f190d92d382'
PROOF = 'c60417b4efd8f2859436974e7e4c1d2eee1cad4d0c06022474fd9ecc6ec7ea59'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def need(ok, msg):
    if not ok:
        raise ValueError(msg)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def record(path):
    need(stat.S_ISREG(path.lstat().st_mode), 'not a regular file: ' + str(path))
    b = path.read_bytes()
    return {'bytes': len(b), 'sha256': sha(b)}


def unique(pairs):
    d = {}
    for k, v in pairs:
        need(k not in d, 'duplicate JSON key: ' + k)
        d[k] = v
    return d


def readjson(path):
    record(path)
    return json.loads(path.read_bytes(), object_pairs_hook=unique)


def safe(s):
    p = PurePosixPath(s)
    need(isinstance(s, str) and str(p) == s and not p.is_absolute() and '..' not in p.parts and s != '.', 'unsafe relative path')
    return p


def inventory(root):
    need(stat.S_ISDIR(root.lstat().st_mode), 'not a directory: ' + str(root))
    files, dirs = {}, ['.']
    for base, children, names in os.walk(root, followlinks=False):
        for n in children + names:
            p = Path(base) / n
            rel = p.relative_to(root).as_posix()
            safe(rel)
            m = p.lstat().st_mode
            if stat.S_ISDIR(m):
                dirs.append(rel)
            elif stat.S_ISREG(m):
                files[rel] = record(p)
            else:
                raise ValueError('nonregular entry: ' + str(p))
    return {'directories': sorted(dirs), 'files': files}


def check_packet(packet, anchor, schema):
    inv = inventory(packet)
    need(inv['files'].pop('MANIFEST.json')['sha256'] == anchor, 'detached manifest hash mismatch')
    m = readjson(packet / 'MANIFEST.json')
    need(m['schema'] == schema, 'manifest schema mismatch')
    need(m['files'] == inv['files'], 'exact payload names/bytes/sizes mismatch')
    need(m['directories'] == inv['directories'], 'exact directory set mismatch')
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--project-root', type=Path, required=True)
    ap.add_argument('--expected-final', required=True)
    ap.add_argument('--expected-report', required=True)
    a = ap.parse_args()
    for h in (a.expected_final, a.expected_report):
        need(re.fullmatch('[0-9a-f]{64}', h) is not None, 'invalid external anchor')
    root, project = a.root, a.project_root
    need(stat.S_ISDIR(root.lstat().st_mode), 'review root type')
    packet = root / 'packet'
    own = check_packet(packet, a.expected_final, 't096n126-correctness-r1-v1')
    for name in ('FINAL', 'REPORT.md', 'REPORT.sha256'):
        record(root / name)
    need((root / 'FINAL').read_text() == a.expected_final + '\n', 'outside FINAL mismatch')
    need(record(root / 'REPORT.md')['sha256'] == a.expected_report, 'outside REPORT mismatch')
    need((root / 'REPORT.sha256').read_text() == a.expected_report + '\n', 'REPORT digest text mismatch')
    need((root / 'REPORT.md').read_bytes() == (packet / 'public/handoff.md').read_bytes(), 'handoff differs from outside report')
    reg = readjson(packet / 'private/input-register.json')
    by_original = {}
    for row in reg:
        src = project / safe(row['original'])
        snap = packet / safe(row['snapshot'])
        expected = {'bytes': row['bytes'], 'sha256': row['sha256']}
        need(record(snap) == expected, 'snapshot mismatch: ' + row['snapshot'])
        need(record(src) == expected, 'immutable original changed: ' + row['original'])
        need(row['original'] not in by_original, 'duplicate original')
        by_original[row['original']] = snap
    original = readjson(packet / 'private/author-original-inventory.json')
    author = project / safe(original['root'])
    baseline = {'files': original['files'], 'directories': original['directories']}
    need(inventory(author) == baseline, 'whole actual author root changed')
    author_manifest = check_packet(author / 'packet', AUTHOR_FINAL, 'r126-exact-packet-v1')
    need(author_manifest['pin'] == PIN, 'author pin mismatch')
    need(record(author / 'REPORT.md')['sha256'] == AUTHOR_REPORT, 'author report mismatch')
    need((author / 'FINAL').read_text() == AUTHOR_FINAL + '\n', 'author FINAL semantics mismatch')
    for n, h in [('FROZEN.md', SCOPE), ('proof.md', PROOF)]:
        need(record(author / 'packet/public' / n)['sha256'] == h, 'author ' + n + ' mismatch')
    freeze = readjson(author / 'packet/public/freeze-anchor.json')
    need((author / 'freeze-anchor.json').read_bytes() == (author / 'packet/public/freeze-anchor.json').read_bytes(), 'freeze copies differ')
    for n, h in freeze['files'].items():
        need(record(author / 'packet/public' / safe(n))['sha256'] == h, 'prefreeze identity mismatch')
    upstream = readjson(by_original['sources/upstream.json'])
    need(upstream['commit'] == PIN, 'source pin mismatch')
    tree_path = by_original['sources/preprints-tree.json']
    need(record(tree_path)['sha256'] == TREE, 'canonical tree digest mismatch')
    tree = readjson(tree_path)
    need(tree['truncated'] is False and len(tree['tree']) == 13223, 'tree completeness mismatch')
    entries = {x['path']: x for x in tree['tree']}
    mapping = readjson(author / 'packet/public/source-map.json')
    selected = {'096-0-main.tex', '096-0-sections__extremizers.tex', 'companion-kernel-application.tex', 'companion-07-consequences.tex'}
    checked = 0
    for row in mapping:
        if Path(row['file']).name not in selected:
            continue
        body = author / 'packet' / safe(row['file'])
        data = body.read_bytes()
        canonical = row['canonical']
        ent = entries[canonical['path']]
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        need(sha(data) == row['sha256'], 'selected source SHA256 mismatch')
        need(blob == canonical['sha'] == ent['sha'], 'selected source Git identity mismatch')
        need(len(data) == canonical['size'] == ent['size'], 'selected source size mismatch')
        need(row['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + canonical['path'], 'selected source URL mismatch')
        checked += 1
    need(checked == 4, 'selected source count mismatch')
    history = readjson(author / 'packet/private/history/register.json')
    for row in history[:4]:
        need(record(author / 'packet' / safe(row['file'])) == record(project / safe(row['source'])), 'inherited history copy differs from actual body')
    print(json.dumps({'artifact_verification': 'PASS', 'mathematical_test': False,
                      'own_payload_files': len(own['files']), 'immutable_input_snapshots': len(reg),
                      'whole_author_files_unchanged': len(original['files']),
                      'selected_pinned_bodies': checked, 'tree_entries': 13223,
                      'contract': 'Exact bytes, sizes, names, directory names and regular-entry types; no permission-mode or hardlink-count binding.'}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        sys.exit(1)
