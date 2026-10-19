#!/usr/bin/env python3
"""Authenticate this review's bytes and selected evidence; never decide mathematics."""
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
    'FINAL.json': 'b177b36d6ef39750a4621d0fd1f4c73a5d4891c74fc0cd6d9041b0d5eb7aa41e',
    'REPORT.md': 'b89f5d434fca85f54757202e50959546c6224f8ac7beadac3d75cd64dfb4cee4',
    'packet/MANIFEST.json': '4c6aaaa4b6c31dccd03ca58677bd3279f6de0646f3366e7341493d32b20de6cc',
    'copied-controls/receipt.json': 'd611270809d28962ac8a66b4636a2b2565546d99994cce6292c581a12a1ef454',
    'packet/public/FROZEN-SCOPE.md': 'ec09396badbea0351a0eb2f8bdb7b780e1d74ffdace92bb04114cccdc5be4a22',
    'packet/public/proof.md': 'fc725dd2d70ca3a5a52bcfdca7da954e674a3157353b831dd2caf6badd097881',
}


def guard(event, args):
    if event == 'open':
        mode, flags = args[1:3]
        if ((isinstance(mode, str) and any(c in mode for c in 'wax+')) or
                (isinstance(flags, int) and flags &
                 (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND))):
            raise PermissionError('read-only guard: write denied')
    if event.startswith(('subprocess.', 'socket.')) or event in {
        'os.system', 'os.exec', 'os.posix_spawn', 'os.fork', 'os.remove',
        'os.rename', 'os.rmdir', 'os.mkdir', 'os.chmod', 'os.link',
        'os.symlink', 'os.truncate', 'os.utime',
    }:
        raise PermissionError('read-only guard: operation denied ' + event)


sys.addaudithook(guard)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relative(value):
    need(isinstance(value, str) and value and '\\' not in value, 'invalid path')
    need(not PurePosixPath(value).is_absolute() and
         all(x not in ('', '.', '..') for x in value.split('/')), 'unsafe path')
    return value


def read(path):
    info = path.lstat()
    need(stat.S_ISREG(info.st_mode), 'nonregular file: ' + str(path))
    need(info.st_nlink == 1, 'hardlinked file: ' + str(path))
    need(info.st_mode & 0o444, 'unreadable file mode: ' + str(path))
    return path.read_bytes()


def inventory(root):
    files, directories = {}, {}

    def walk(path, key):
        info = path.lstat()
        need(stat.S_ISDIR(info.st_mode), 'non-directory: ' + str(path))
        need(info.st_mode & 0o444 and info.st_mode & 0o111, 'inaccessible directory')
        directories[key] = stat.S_IMODE(info.st_mode)
        for child in sorted(path.iterdir()):
            name = child.relative_to(root).as_posix()
            child_info = child.lstat()
            if stat.S_ISDIR(child_info.st_mode):
                walk(child, name)
            else:
                data = read(child)
                files[name] = {'sha256': digest(data), 'bytes': len(data),
                               'mode': stat.S_IMODE(child_info.st_mode)}

    walk(root, '.')
    return files, directories


def check(root, finalhash, reporthash):
    for value in (finalhash, reporthash):
        need(re.fullmatch('[0-9a-f]{64}', value), 'invalid detached hash')
    need(stat.S_ISDIR(root.lstat().st_mode), 'root must be a real directory')
    final_bytes = read(root / 'FINAL.json')
    need(digest(final_bytes) == finalhash, 'detached FINAL mismatch')
    final = json.loads(final_bytes)
    report = read(root / 'REPORT.md')
    need(digest(report) == reporthash == final['report_sha256'], 'detached REPORT mismatch')
    need(final['pin'] == PIN and final['target'] == 'T238B125', 'review identity mismatch')
    need(final['verdict'] == 'PASS' and final['scope'] == 'entire original frozen theorem',
         'verdict/scope mismatch')
    need(final['contribution_verdict'] is None and final['count_assignment'] is None
         and final['acceptance_assignment'] is None, 'unauthorized assignment')
    packet = root / 'packet'
    manifest_bytes = read(packet / 'MANIFEST.json')
    need(digest(manifest_bytes) == final['manifest_sha256'], 'manifest hash mismatch')
    need(stat.S_IMODE((packet / 'MANIFEST.json').lstat().st_mode) == final['manifest_mode'],
         'manifest mode mismatch')
    manifest = json.loads(manifest_bytes)
    need(manifest['version'] == 1, 'manifest version mismatch')
    for name in manifest['files']:
        relative(name)
    for name in manifest['directories']:
        if name != '.':
            relative(name)
    files, directories = inventory(packet)
    need(set(files) == set(manifest['files']) | {'MANIFEST.json'}, 'exact file membership mismatch')
    need(directories == manifest['directories'], 'directory membership/mode mismatch')
    need('MANIFEST.json' not in manifest['files'], 'manifest cannot include itself')
    for name, record in manifest['files'].items():
        need(files[name] == record, 'payload mismatch: ' + name)
    for name, value in final['payload_anchors'].items():
        need(files[relative(name)]['sha256'] == value, 'payload anchor mismatch')
    need(b'**Verdict: PASS,' in read(packet / 'public/review.md'), 'review verdict declaration mismatch')

    inputs = json.loads(read(packet / 'private/input-register.json'))
    names = set()
    for record in inputs:
        name = relative(record['local'])
        need(name not in names, 'duplicate input record')
        names.add(name)
        data = read(packet / name)
        need(len(data) == record['bytes'] and digest(data) == record['sha256'],
             'input binding mismatch: ' + name)
    need(json.loads(read(packet / 'private/author-anchors.json')) == AUTHOR,
         'author anchor record mismatch')
    for name, value in AUTHOR.items():
        need(digest(read(packet / 'private/author' / name)) == value,
             'author detached anchor mismatch: ' + name)
    status = json.loads(read(packet / 'private/handoff/task-status.json'))
    need(status['status'] == 'completed' and status['workState'] == 'result_available'
         and status['hasPendingChildRuns'] is False, 'author terminal status mismatch')
    for name in ('FINAL.json', 'REPORT.md', 'packet/MANIFEST.json', 'copied-controls/receipt.json'):
        need(AUTHOR[name] in status['summary'] and AUTHOR[name] in status['latestTerminalSummary'],
             'saved terminal handoff anchor mismatch')

    tree_bytes = read(packet / 'private/context/preprints-tree.json')
    need(digest(tree_bytes) == TREE, 'canonical tree digest mismatch')
    tree = json.loads(tree_bytes)
    need(tree['truncated'] is False and len(tree['tree']) == 13223, 'canonical tree extent mismatch')
    canonical = {record['path']: record for record in tree['tree']}
    need(len(canonical) == 13223, 'duplicate canonical path')
    sources = json.loads(read(packet / 'private/source-register.json'))
    need(len(sources) == 6, 'selected source count mismatch')
    seen = set()
    for record in sources:
        source = record['canonical']
        name = source['path']
        need(name not in seen and source == canonical[name], 'canonical record mismatch')
        seen.add(name)
        need(record['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + name,
             'pinned raw URL mismatch')
        need(record['local'] == 'private/upstream/' + name, 'source placement mismatch')
        data = read(packet / relative(record['local']))
        need(len(data) == source['size'] and digest(data) == record['sha256'], 'source size/hash mismatch')
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        need(blob == source['sha'], 'canonical Git blob mismatch')
        need(len(data.splitlines()) == record['lines'], 'source line extent mismatch')
    return {'status': 'REVIEW_ARTIFACTS_AUTHENTICATED_ONLY', 'payload_files': len(manifest['files']),
            'selected_pinned_sources': len(sources), 'retained_input_records': len(inputs),
            'canonical_entries': len(canonical), 'mathematical_verdict_recomputed': False,
            'contribution_or_count_assigned': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--finalhash', required=True)
    parser.add_argument('--reporthash', required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.root, args.finalhash, args.reporthash), sort_keys=True))
        return 0
    except Exception as exc:
        print(json.dumps({'status': 'REJECT', 'reason': str(exc)}, sort_keys=True))
        return 1


if __name__ == '__main__':
    sys.exit(main())
