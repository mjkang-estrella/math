#!/usr/bin/env python3
"""Independent read-only r93 artifact verifier. Original reviewer code, MIT.

Checks integrity only. stdout is its only output; it does not import author code.
No claim of hostile-runtime or race resistance.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
ANCHOR = '362dfe44e0db3abcddf9ce56f2a86f496e1e9c47297bf85c6e922847e760c479'

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

def safe(root, name):
    p = PurePosixPath(name)
    require(name and not p.is_absolute() and '..' not in p.parts and '\\' not in name and str(p) == name, 'unsafe path')
    q = root
    for part in p.parts:
        q = q / part
        require(not q.is_symlink(), 'symlink')
    return q

def audit(event, args):
    if event == 'open':
        mode, flags = args[1:3]
        require(not (isinstance(mode, str) and any(c in mode for c in 'wax+')), 'write open denied')
        require(not (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)), 'write flags denied')
    require(event not in {'os.remove', 'os.unlink', 'os.rename', 'os.rmdir', 'os.mkdir', 'os.chmod', 'os.chown', 'os.link', 'os.symlink', 'os.truncate', 'os.utime', 'subprocess.Popen', 'os.system'}, 'mutation/process denied')

def verify(root, anchor, tree_path):
    require(root.is_dir() and not root.is_symlink(), 'root type')
    require(digest(safe(root, 'FINAL.json')) == anchor, 'detached FINAL mismatch')
    final = read(root / 'FINAL.json')
    require(final['pin'] == PIN and final['schema'] == 'arithmetic-r93-v1', 'pin/schema')
    require(digest(safe(root, 'REPORT.md')) == final['report_sha256'], 'report mismatch')
    for name, rec in final['root_files'].items():
        p = safe(root, name)
        require(p.is_file() and p.stat().st_size == rec['bytes'] and digest(p) == rec['sha256'], 'root file mismatch')
    packet = safe(root, 'packet')
    require(digest(safe(packet, 'MANIFEST.json')) == final['manifest_sha256'], 'manifest mismatch')
    manifest = read(packet / 'MANIFEST.json')
    files, dirs = {}, {'.': packet}
    for base, subdirs, names in os.walk(packet, followlinks=False):
        for name in subdirs:
            p = Path(base) / name
            require(stat.S_ISDIR(p.lstat().st_mode), 'non-directory')
            dirs[p.relative_to(packet).as_posix()] = p
        for name in names:
            p = Path(base) / name
            require(stat.S_ISREG(p.lstat().st_mode), 'non-regular file')
            if p != packet / 'MANIFEST.json':
                files[p.relative_to(packet).as_posix()] = p
    require(set(files) == set(manifest['files']), 'file membership')
    require(set(dirs) == set(manifest['directories']) == set(manifest['directory_modes']), 'directory membership')
    for name, p in files.items():
        rec, st = manifest['files'][name], p.stat()
        require(st.st_size == rec['bytes'] and digest(p) == rec['sha256'], 'payload bytes: ' + name)
        require(stat.S_IMODE(st.st_mode) == rec['mode'] and st.st_nlink == rec['nlink'] == 1, 'payload mode/links')
    for name, p in dirs.items():
        require(stat.S_IMODE(p.stat().st_mode) == manifest['directory_modes'][name], 'directory mode')
    require(digest(packet / 'public/FROZEN.md') == final['frozen_sha256'], 'frozen mismatch')
    freeze = read(packet / 'public/freeze.json')
    require(freeze['sha256'] == final['frozen_sha256'] and freeze['frozen_path'] == 'public/FROZEN.md', 'freeze receipt')
    copied_tree = packet / 'private/context/sources/preprints-tree.json'
    require(digest(copied_tree) == digest(tree_path) == TREE == final['tree_sha256'], 'canonical tree hash')
    tree = read(copied_tree)
    require(tree['truncated'] is False and len(tree['tree']) == 13223, 'canonical completeness')
    entries = {x['path']: x for x in tree['tree']}
    require(len(entries) == 13223, 'duplicate canonical path')
    canonical = read(packet / 'public/canonical.json')
    require(len(canonical) == len({x['canonical']['path'] for x in canonical}) == 22, 'canonical count')
    for row in canonical:
        c = row['canonical']
        require(entries[c['path']] == c and c['type'] == 'blob', 'canonical metadata')
        require(row['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + c['path'], 'canonical URL')
        b = safe(packet, row['local']).read_bytes()
        require(len(b) == c['size'] and hashlib.sha256(b).hexdigest() == row['sha256'], 'canonical bytes')
        require(hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == c['sha'], 'canonical git blob')
    primary = [x for x in read(packet / 'public/primary.json') if 'failure' not in x]
    require(len(primary) == 4, 'primary count')
    for row in primary:
        require(digest(safe(packet, row['pdf'])) == row['sha256'] and digest(safe(packet, row['text'])) == row['text_sha256'], 'primary bytes')
    for category, count in [('history', 28), ('context', 5)]:
        rows = read(packet / ('public/' + category + '.json'))
        require(len(rows) == count, 'copy count')
        for row in rows:
            p = safe(packet, row['local'])
            require(p.stat().st_size == row['bytes'] and digest(p) == row['sha256'], 'copy bytes')
    return {'status': 'INTEGRITY_ONLY_OK', 'payloads': len(files), 'directories': len(dirs), 'canonical_bodies': 22, 'primary_pairs': 4, 'history_copies': 28, 'context_copies': 5, 'mathematical_gate': False}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--tree', required=True, type=Path)
    parser.add_argument('--final-sha256', required=True)
    args = parser.parse_args()
    sys.addaudithook(audit)
    try:
        print(json.dumps(verify(args.root, args.final_sha256, args.tree), sort_keys=True))
    except Exception as exc:
        print(json.dumps({'status': 'REJECT', 'reason': str(exc)}))
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
