#!/usr/bin/env python3
"""Read-only r91 artifact verifier. Detached anchors are mandatory. MIT."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

sys.dont_write_bytecode = True


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def regular(path):
    st = path.lstat()
    require(stat.S_ISREG(st.st_mode) and st.st_nlink == 1,
            'nonregular, symlink or hardlinked file: ' + str(path))
    return st


def safe_rel(value):
    p = PurePosixPath(value)
    require(not p.is_absolute() and str(p) == value and
            value not in ('', '.') and '..' not in p.parts, 'unsafe relative path')
    return value


def inventory(root):
    files, dirs = {}, {}
    for dp, dns, fns in os.walk(root, followlinks=False):
        p = Path(dp)
        st = p.lstat()
        require(stat.S_ISDIR(st.st_mode), 'non-directory in packet')
        dirs[str(p.relative_to(root))] = stat.S_IMODE(st.st_mode)
        for name in dns:
            require(stat.S_ISDIR((p / name).lstat().st_mode), 'symlink/non-directory entry')
        for name in fns:
            f = p / name
            s = regular(f)
            rel = str(f.relative_to(root))
            if rel == 'MANIFEST.json':
                continue
            files[rel] = {'sha256': sha(f), 'bytes': s.st_size,
                          'mode': stat.S_IMODE(s.st_mode)}
    return {'files': files, 'directories': dirs}


def verify(root, tree_path, final_hash, report_hash):
    root = root.absolute()
    for p in (root, *root.parents):
        require(stat.S_ISDIR(p.lstat().st_mode), 'symlink/non-directory ancestor')
    for h in (final_hash, report_hash):
        require(len(h) == 64 and all(c in '0123456789abcdef' for c in h),
                'invalid detached anchor')
    regular(root / 'FINAL.json')
    require(sha(root / 'FINAL.json') == final_hash, 'detached FINAL mismatch')
    final = json.loads((root / 'FINAL.json').read_text())
    require(final['status'] == 'PREFREEZE_NO_NOMINEE' and final['frozen_target'] is None,
            'unexpected archive status')
    regular(root / 'REPORT.md')
    require(sha(root / 'REPORT.md') == report_hash == final['report_sha256'],
            'detached REPORT mismatch')
    packet = root / 'packet'
    regular(packet / 'MANIFEST.json')
    require(sha(packet / 'MANIFEST.json') == final['manifest_sha256'], 'manifest anchor mismatch')
    manifest = json.loads((packet / 'MANIFEST.json').read_text())
    for rel in manifest['files']:
        safe_rel(rel)
    for rel in manifest['directories']:
        if rel != '.':
            safe_rel(rel)
    require(inventory(packet) == manifest, 'exact packet inventory mismatch')
    for rel, digest in final['code_sha256'].items():
        require(sha(packet / safe_rel(rel)) == digest, 'code binding mismatch')
    require(sha(packet / 'public/report.md') == final['public_report_sha256'],
            'public report binding mismatch')
    regular(tree_path)
    require(sha(tree_path) == final['tree_sha256'], 'external tree anchor mismatch')
    require(sha(packet / 'private/context/preprints-tree.json') == final['tree_sha256'],
            'copied tree mismatch')
    tree = json.loads(tree_path.read_text())
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'incomplete tree')
    bypath = {x['path']: x for x in tree['tree']}
    require(len(bypath) == 13223, 'duplicate tree paths')
    pin = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    require(final['pin'] == pin, 'wrong pin')
    rows = json.loads((packet / 'public/canonical.json').read_text())
    require(len({r['local'] for r in rows}) == len(rows), 'duplicate canonical destinations')
    for r in rows:
        c = r['canonical']
        require(bypath.get(c['path']) == c and c['type'] == 'blob', 'canonical metadata mismatch')
        require(r['url'] == 'https://raw.githubusercontent.com/openai/math/' + pin + '/' + c['path'],
                'unpinned source URL')
        data = (packet / safe_rel(r['local'])).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(len(data) == c['size'] and blob == c['sha'] and
                hashlib.sha256(data).hexdigest() == r['sha256'], 'canonical body mismatch')
    primaries = json.loads((packet / 'public/primary.json').read_text())
    for r in primaries:
        require('failure' not in r, 'unexpected primary failure')
        for kind in ('pdf', 'text'):
            require(sha(packet / safe_rel(r[kind])) == r[kind + '_sha256'], 'primary pair mismatch')
    history = json.loads((packet / 'public/history.json').read_text())
    for r in history:
        f = packet / safe_rel(r['local'])
        require(sha(f) == r['sha256'] and f.stat().st_size == r['bytes'], 'history body mismatch')
    return {'status': 'INTEGRITY_ONLY_OK', 'payload_files': len(manifest['files']),
            'directories': len(manifest['directories']), 'canonical_blobs': len(rows),
            'primary_pairs': len(primaries), 'history_copies': len(history)}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--tree', type=Path, required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    try:
        print(json.dumps(verify(args.root, args.tree, args.final_sha256, args.report_sha256), sort_keys=True))
    except Exception as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        sys.exit(1)
