#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only detached integrity verifier; not a mathematical proof checker."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import re
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError('duplicate JSON key')
        out[key] = value
    return out


def parse(data):
    return json.loads(data, object_pairs_hook=unique)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    arg = argparse.ArgumentParser()
    arg.add_argument('--seal-sha256', required=True)
    a = arg.parse_args()
    require(re.fullmatch('[0-9a-f]{64}', a.seal_sha256), 'invalid anchor')
    root = Path(__file__).resolve().parent
    # No writes, subprocesses or network are needed or permitted by this code.
    nodes = list(root.rglob('*'))
    require(not any(p.is_symlink() for p in nodes), 'symlink')
    require(all(p.is_file() or p.is_dir() for p in nodes), 'nonregular entry')
    seal_bytes = (root / 'seal.json').read_bytes()
    require(digest(seal_bytes) == a.seal_sha256, 'external seal anchor mismatch')
    seal = parse(seal_bytes)
    manifest_bytes = (root / 'manifest.json').read_bytes()
    require(digest(manifest_bytes) == seal['manifest_sha256'], 'manifest mismatch')
    manifest = parse(manifest_bytes)
    listed = manifest['files']
    actual = {str(p.relative_to(root)) for p in nodes if p.is_file()}
    require(actual == set(listed) | {'manifest.json', 'seal.json'}, 'file membership mismatch')
    dirs = {str(p.relative_to(root)) for p in nodes if p.is_dir()}
    require(dirs == set(manifest['directories']), 'directory membership mismatch')
    for name, record in listed.items():
        path = Path(name)
        require(not path.is_absolute() and '..' not in path.parts, 'unsafe path')
        data = (root / name).read_bytes()
        require(len(data) == record['size'] and digest(data) == record['sha256'], 'payload mismatch: ' + name)
    load = lambda p: parse((root / p).read_bytes())
    source = load('complete-tree-extract.json')
    require(source['truncated'] is False, 'truncated source tree')
    tree = {x['path']: x for x in source['entries'] if x['type'] == 'blob' and not x['path'].endswith('.pdf')}
    receipts = load('pinned-receipts.json')
    require(len(receipts) == 14 and {x['upstream_path'] for x in receipts} == set(tree), 'source membership mismatch')
    for x in receipts:
        data = (root / x['path']).read_bytes()
        require(digest(data) == x['sha256'] and len(data) == x['size'], 'source receipt mismatch')
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == x['blob'] == tree[x['upstream_path']]['sha'], 'Git blob mismatch')
        require(x['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + x['upstream_path'], 'unpinned source URL')
    primary = load('primary-receipts.json')
    for ext, key in [('pdf', 'pdf_sha256'), ('txt', 'text_sha256')]:
        require(digest((root / ('inputs/private/primary/huang-yau-2102.00963v3.' + ext)).read_bytes()) == primary[key], 'primary receipt mismatch')
    s = load('scale-check.json')
    a, c = Fraction(s['a']), Fraction(s['girth_coefficient'])
    exponent = -Fraction(1, 3) + 20 * a + c
    require(exponent == Fraction(s['collision_exponent']) < 0, 'collision exponent')
    require(0 < c < Fraction(s['source_girth_exponent']) == Fraction(2, 1000) * a, 'girth margin')
    status = load('status.json')
    require(status['status'] == 'TECHNICAL_SCREEN_ONLY' and not status['target_frozen'] and not status['nominee'] and not status['independent_pass'] and status['count_added'] == 0, 'status mismatch')
    print(json.dumps({'integrity': 'PASS', 'payloads': len(listed), 'directories': len(dirs), 'pinned_blobs': len(receipts), 'scalar_exponent': str(exponent), 'mathematical_or_contribution_PASS': False}))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
