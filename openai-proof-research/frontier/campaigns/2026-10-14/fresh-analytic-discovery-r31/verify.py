#!/usr/bin/env python3
# Copyright (c) Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only packet identity verification; no mathematical correctness claim."""
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys
import io
import tarfile

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
ROOT = Path(__file__).resolve().parent

def check(condition, message):
    if not condition:
        raise ValueError(message)

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def relative_path(value):
    p = Path(value)
    check(not p.is_absolute() and '..' not in p.parts and str(p) == value,
          'unsafe or noncanonical relative path')
    return ROOT / p

def main():
    check(len(sys.argv) == 2 and re.fullmatch(r'[0-9a-f]{64}', sys.argv[1]),
          'usage: python -B verify.py EXTERNAL_MANIFEST_SHA256')
    manifest_bytes = (ROOT / 'manifest.json').read_bytes()
    check(sha256(manifest_bytes) == sys.argv[1], 'external manifest anchor mismatch')
    manifest = json.loads(manifest_bytes)
    check(manifest['pin'] == PIN and manifest['status'] == 'no-nominee',
          'unexpected pin/status')
    files, directories = {}, []
    for p in sorted(ROOT.rglob('*')):
        check(not p.is_symlink(), 'symlinks are forbidden')
        rel = p.relative_to(ROOT).as_posix()
        if p.is_dir():
            directories.append(rel)
        elif p.is_file():
            if rel != 'manifest.json':  # exclude only the ROOT envelope
                data = p.read_bytes()
                files[rel] = {'sha256': sha256(data), 'bytes': len(data)}
        else:
            raise ValueError('nonregular filesystem object')
    check(files == manifest['files'], 'exact file inventory/content mismatch')
    check(directories == manifest['directories'], 'exact directory inventory mismatch')
    tree = json.loads((ROOT / 'private/context/preprints-tree.json').read_bytes())
    check(tree.get('truncated') is False and len(tree['tree']) == 13223,
          'complete pinned tree contract mismatch')
    entries = {x['path']: x for x in tree['tree']}
    upstream = json.loads((ROOT / 'private/context/upstream.json').read_bytes())
    check(upstream['commit'] == PIN, 'upstream pin mismatch')
    sources = json.loads((ROOT / 'source-receipts.json').read_bytes())
    seen = set()
    for receipt in sources:
        check(receipt['path'] not in seen, 'duplicate source receipt')
        seen.add(receipt['path'])
        data = relative_path(receipt['local']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        entry = entries[receipt['path']]
        check(entry['type'] == 'blob' and entry['sha'] == blob == receipt['git_blob'],
              'source Git blob mismatch')
        check(sha256(data) == receipt['sha256'], 'source SHA256 mismatch')
        check(receipt['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + receipt['path'],
              'source pinned URL mismatch')
    primaries = json.loads((ROOT / 'primary-receipts.json').read_bytes())
    expected_urls = {'chen-he': 'https://arxiv.org/src/math/0603523v3',
                     'huang-zheng': 'https://arxiv.org/src/1007.4571v2',
                     'humbert': 'https://arxiv.org/src/2409.11197v3'}
    check({p['name'] for p in primaries} == set(expected_urls), 'primary set mismatch')
    check(len(primaries) == len(expected_urls), 'duplicate primary receipt')
    for receipt in primaries:
        data = relative_path(receipt['local']).read_bytes()
        check(sha256(data) == receipt['sha256'], 'primary download hash mismatch')
        check(receipt['url'] == expected_urls[receipt['name']], 'primary version URL mismatch')
        if receipt['encoding'] == 'gzip-single-tex':
            check(gzip.decompress(data) == relative_path(receipt['decompressed_local']).read_bytes(),
                  'primary decompression mismatch')
        elif receipt['encoding'] == 'tar':
            with tarfile.open(fileobj=io.BytesIO(data)) as archive:
                members = [m for m in archive.getmembers() if m.isfile() and m.name.endswith(('.tex', '.bib'))]
                check([m.name for m in members] == receipt['members'], 'primary member inventory mismatch')
                for member in members:
                    path = receipt['member_root'] + '/' + member.name
                    check(archive.extractfile(member).read() == relative_path(path).read_bytes(),
                          'primary archive member mismatch')
        else:
            raise ValueError('unknown primary encoding')
    print(json.dumps({'status': 'PASS', 'files': len(files), 'directories': len(directories),
                      'pinned_blobs': len(sources), 'primary_downloads': len(primaries),
                      'manifest_sha256': sys.argv[1], 'mathematical_verdict': 'none'}))

if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        sys.exit(1)
