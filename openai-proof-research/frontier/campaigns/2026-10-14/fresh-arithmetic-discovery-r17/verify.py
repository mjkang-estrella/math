#!/usr/bin/env python3
"""Offline, read-only identity verifier; no mathematical verdict."""
import argparse
import hashlib
import json
from pathlib import Path
import stat
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def fail(message):
    raise ValueError(message)


def safe(root, name):
    p = Path(name)
    if p.is_absolute() or '..' in p.parts or not p.parts:
        fail('unsafe inventory path')
    target = root / p
    if target.is_symlink() or not target.is_file():
        fail('missing or nonregular payload: ' + name)
    return target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--checkpoint-sha256', required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    raw = safe(root, 'manifest.json').read_bytes()
    if digest(raw) != args.manifest_sha256:
        fail('external manifest anchor mismatch')
    if digest(safe(root, 'checkpoint.md').read_bytes()) != args.checkpoint_sha256:
        fail('external checkpoint anchor mismatch')
    manifest = json.loads(raw)
    actual_files = []
    actual_dirs = []
    for p in root.rglob('*'):
        mode = p.lstat().st_mode
        name = p.relative_to(root).as_posix()
        if stat.S_ISLNK(mode):
            fail('symlink not allowed: ' + name)
        if stat.S_ISDIR(mode):
            actual_dirs.append(name)
        elif stat.S_ISREG(mode):
            if name != 'manifest.json':
                actual_files.append(name)
        else:
            fail('special file not allowed: ' + name)
    expected = manifest['files']
    if sorted(actual_files) != sorted(expected):
        fail('payload membership mismatch')
    if sorted(actual_dirs) != manifest['directories']:
        fail('directory membership mismatch')
    for name, item in expected.items():
        data = safe(root, name).read_bytes()
        if len(data) != item['size'] or digest(data) != item['sha256']:
            fail('payload bytes mismatch: ' + name)
    pin = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    context_root = root / 'private/context'
    upstream = json.loads((context_root / 'sources/upstream.json').read_text())
    if upstream['commit'] != pin:
        fail('unexpected source pin')
    tree = json.loads((context_root / 'sources/preprints-tree.json').read_text())
    if tree.get('truncated') is not False:
        fail('source path tree is truncated')
    blobs = {e['path']: e['sha'] for e in tree['tree'] if e['type'] == 'blob'}
    receipts = json.loads((root / 'receipts.json').read_text())
    for item in receipts:
        data = safe(root, item['path']).read_bytes()
        gh = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if gh != item['git_blob'] or gh != blobs[item['upstream']]:
            fail('pinned Git blob mismatch')
        if digest(data) != item['sha256'] or len(data) != item['size']:
            fail('source receipt mismatch')
        if item['url'] != 'https://raw.githubusercontent.com/openai/math/' + pin + '/' + item['upstream']:
            fail('nonpinned source URL')
    primaries = json.loads((root / 'primary-receipts.json').read_text())
    for item in primaries:
        p = safe(root, item['path'])
        if digest(p.read_bytes()) != item['sha256']:
            fail('primary PDF receipt mismatch')
        if digest(p.with_suffix('.txt').read_bytes()) != item['text_sha256']:
            fail('primary text receipt mismatch')
    contexts = json.loads((root / 'context-receipts.json').read_text())
    for item in contexts:
        data = safe(root, item['path']).read_bytes()
        if digest(data) != item['sha256'] or len(data) != item['size']:
            fail('context snapshot receipt mismatch')
    print(json.dumps({'status': 'IDENTITY_PASS_ONLY', 'files': len(expected),
                      'directories': len(actual_dirs), 'pinned_blobs': len(receipts),
                      'primary_pdfs': len(primaries), 'context_snapshots': len(contexts),
                      'mathematical_proof': False, 'nomination': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('REJECT: ' + str(exc), file=sys.stderr)
        sys.exit(1)
