#!/usr/bin/env python3
"""Read-only identity verification; no mathematical, priority or acceptance gate.
The reviewmanifest argument MUST come independently from the review handoff.
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
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
AUTHOR = {
    'packet/manifest.json': '114968b75d11c48f60e4c76d722396ecf5da8b906e5ece393ec70efe464f12d3',
    'FINAL.json': '002f8c79e8aa95cf4429b5a3e1360cde7079e9410b9ea8709ff3a5f95351d24a',
    'packet/public/research-report.md': '7390b2cc617f29fef747d7664946d4a83f9e17db86c006baa6417dcd341bbac5',
    'packet/public/frozen-target.md': 'bab65e89a8a02cd2d5083ee5c97a293dca4b51a34be1077c3fedf4d1a880eb81',
    'packet/public/proof.md': 'ebaa6730fc7c7e8a0ec9155747c11f17e84c7f1c4a068afb824382c84362c462',
    'packet/public/verify.py': '1a3f0d59326eecc501fd63c9e47982231dac1377ef7c2a3941deb1c4c360207b',
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    result = {}
    for k, v in pairs:
        if k in result:
            raise ValueError('duplicate JSON key')
        result[k] = v
    return result


def read_regular(p):
    s = p.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
        raise ValueError('nonregular, symlink or hard-linked file: ' + p.name)
    return p.read_bytes()


def safe(name):
    if not isinstance(name, str) or not name or '\\' in name:
        raise ValueError('invalid member path')
    p = PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or p.as_posix() != name or name == '.':
        raise ValueError('unsafe member path')


def inventory(root):
    s = root.lstat()
    if not stat.S_ISDIR(s.st_mode) or root.is_symlink():
        raise ValueError('root must be a real directory')
    files, directories = {}, {}
    for current, subdirs, names in os.walk(root, followlinks=False):
        for name in subdirs + names:
            p = Path(current) / name
            q = p.relative_to(root).as_posix()
            safe(q)
            t = p.lstat()
            if stat.S_ISDIR(t.st_mode):
                directories[q] = stat.S_IMODE(t.st_mode)
            elif stat.S_ISREG(t.st_mode) and t.st_nlink == 1:
                files[q] = {'mode': stat.S_IMODE(t.st_mode), 'bytes': t.st_size,
                            'sha256': sha(p.read_bytes())}
            else:
                raise ValueError('symlink, hardlink or special member: ' + q)
    return files, directories, stat.S_IMODE(s.st_mode)


def verify_inventory(root, anchor, schema, review=False):
    if not re.fullmatch('[0-9a-f]{64}', anchor):
        raise ValueError('detached anchor must be lowercase SHA256')
    if root.is_symlink():
        raise ValueError('root must be a real directory')
    raw = read_regular(root / 'manifest.json')
    if sha(raw) != anchor:
        raise ValueError('DETACHED manifest anchor mismatch')
    m = json.loads(raw, object_pairs_hook=unique)
    keys = {'schema', 'pin', 'files', 'directories', 'root_mode', 'manifest_mode'}
    if review:
        keys |= {'candidate', 'author_anchors', 'contribution_verdict', 'correctness_gate'}
    if set(m) != keys or m['schema'] != schema or m['pin'] != PIN:
        raise ValueError('manifest schema/pin mismatch')
    if review and (m['candidate'] != 'T152AC116' or m['author_anchors'] != AUTHOR
                   or m['contribution_verdict'] != 'TECHNICAL_CONDITIONAL_ON_CORRECTNESS'
                   or m['correctness_gate'] != 'not assigned'):
        raise ValueError('review scope/anchor/decision binding mismatch')
    if not isinstance(m['files'], dict) or not isinstance(m['directories'], dict):
        raise ValueError('invalid inventory type')
    for name, v in m['files'].items():
        safe(name)
        if name == 'manifest.json' or set(v) != {'mode', 'bytes', 'sha256'}:
            raise ValueError('invalid file record')
        if (type(v['mode']) is not int or type(v['bytes']) is not int or v['bytes'] < 0
                or not re.fullmatch('[0-9a-f]{64}', v['sha256'])):
            raise ValueError('invalid file metadata')
    for name, mode in m['directories'].items():
        safe(name)
        if type(mode) is not int:
            raise ValueError('invalid directory mode')
    files, directories, mode = inventory(root)
    mf = files.pop('manifest.json')
    if mode != m['root_mode'] or mf['mode'] != m['manifest_mode']:
        raise ValueError('root/manifest mode mismatch')
    if files.keys() != m['files'].keys() or directories != m['directories']:
        raise ValueError('exact membership/directory metadata mismatch')
    for name, v in files.items():
        if v != m['files'][name]:
            raise ValueError('payload metadata/hash mismatch: ' + name)
    return m


def verify_author(author, workspace, review):
    if author.is_symlink() or not author.is_dir():
        raise ValueError('author root must be a real directory')
    for name, value in AUTHOR.items():
        if sha(read_regular(author / name)) != value:
            raise ValueError('AUTHOR handoff anchor mismatch: ' + name)
    verify_inventory(author / 'packet', AUTHOR['packet/manifest.json'], 'r116-integrity-v1')
    f = json.loads(read_regular(author / 'FINAL.json'), object_pairs_hook=unique)
    bindings = {'manifest_sha256': 'packet/manifest.json',
                'report_sha256': 'packet/public/research-report.md',
                'proof_sha256': 'packet/public/proof.md',
                'frozen_target_sha256': 'packet/public/frozen-target.md',
                'verifier_sha256': 'packet/public/verify.py'}
    if f['pin'] != PIN or f['schema'] != 'r116-detached-FINAL-v1':
        raise ValueError('AUTHOR FINAL schema/pin mismatch')
    for key, name in bindings.items():
        if f[key] != AUTHOR[name]:
            raise ValueError('AUTHOR FINAL binding mismatch: ' + key)
    receipt = json.loads(read_regular(author / 'packet/public/freeze-receipt.json'),
                         object_pairs_hook=unique)
    if receipt['sha256'] != AUTHOR['packet/public/frozen-target.md']:
        raise ValueError('AUTHOR freeze receipt mismatch')
    before = json.loads(read_regular(review / 'private/author-before.json'), object_pairs_hook=unique)
    observed = {}
    for p in sorted(author.rglob('*')):
        if p.is_file():
            s = p.lstat()
            data = read_regular(p)
            observed[p.relative_to(author).as_posix()] = {
                'bytes': len(data), 'sha256': sha(data), 'mode': stat.S_IMODE(s.st_mode),
                'nlink': s.st_nlink}
    if observed != before:
        raise ValueError('AUTHOR full-root snapshot mismatch')
    raw = read_regular(workspace / 'sources/preprints-tree.json')
    if sha(raw) != TREE:
        raise ValueError('complete-tree anchor mismatch')
    tree = json.loads(raw, object_pairs_hook=unique)
    if tree['truncated'] is not False or len(tree['tree']) != 13223:
        raise ValueError('complete-tree scope mismatch')
    by_path = {v['path']: v for v in tree['tree']}
    if len(by_path) != 13223:
        raise ValueError('duplicate complete-tree paths')
    register = json.loads(read_regular(author / 'packet/public/source-register.json'),
                          object_pairs_hook=unique)
    if len(register['upstream_files']) != 19 or len(register['primary_files']) != 4:
        raise ValueError('source-register extent mismatch')
    for v in register['upstream_files']:
        safe(v['local'])
        data = read_regular(author / 'packet' / v['local'])
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if (blob != v['git_blob'] or blob != by_path[v['path']]['sha']
                or len(data) != v['bytes'] or sha(data) != v['sha256']):
            raise ValueError('canonical Git-blob/SHA256 mismatch')
    for v in register['primary_files']:
        safe(v['file'])
        p = author / 'packet/private/primary' / v['file']
        if sha(read_regular(p)) != v['sha256'] or sha(read_regular(p.with_suffix('.txt'))) != v['text_sha256']:
            raise ValueError('primary PDF/text identity mismatch')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--review', type=Path, required=True)
    p.add_argument('--reviewmanifest', required=True,
                   help='DETACHED external review manifest SHA256 from the handoff')
    p.add_argument('--author', type=Path, required=True)
    p.add_argument('--workspace', type=Path, required=True)
    a = p.parse_args()
    try:
        review, author, workspace = a.review.absolute(), a.author.absolute(), a.workspace.absolute()
        verify_inventory(review, a.reviewmanifest, 't152ac116-contribution-r1-v1', review=True)
        verify_author(author, workspace, review)
    except (OSError, ValueError, TypeError, KeyError) as e:
        print('INTEGRITY REJECT: ' + str(e), file=sys.stderr)
        return 1
    print(json.dumps({'integrity': 'verified', 'candidate': 'T152AC116',
                      'mathematical_gate': False, 'priority_gate': False,
                      'acceptance_gate': False}, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
