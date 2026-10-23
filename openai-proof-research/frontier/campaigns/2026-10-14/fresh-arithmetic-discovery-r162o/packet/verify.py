#!/usr/bin/env python3
"""Read-only exact-packet verifier. Supply independent detached anchors explicitly."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(65536), b''):
            h.update(block)
    return h.hexdigest()


def check_entry(path, size, expected):
    if path.is_symlink():
        return False, 'symlink'
    if not path.is_file():
        return False, 'missing or non-file'
    if path.stat().st_size != size:
        return False, 'size mismatch'
    if digest(path) != expected:
        return False, 'SHA256 mismatch'
    return True, 'match'


def anchor(path, expected):
    if not re.fullmatch('[0-9a-f]{64}', expected):
        raise ValueError('invalid explicit SHA256 anchor')
    if path.is_symlink() or not path.is_file() or digest(path) != expected:
        raise ValueError('detached anchor mismatch: ' + str(path))


def verify(packet, manifest, final, report, manifest_hash, final_hash, report_hash):
    for path, expected in [(manifest, manifest_hash), (final, final_hash), (report, report_hash)]:
        anchor(path, expected)
    if packet.is_symlink() or not packet.is_dir():
        raise ValueError('packet must be a real directory')
    base = packet.resolve()
    data = json.loads(manifest.read_text(encoding='utf-8'))
    if data.get('schema') != 'r162o-exact-packet-v1':
        raise ValueError('unknown manifest schema')
    expected_paths = set()
    total = 0
    for entry in data['files']:
        rel = entry['path']
        p = PurePosixPath(rel)
        if p.is_absolute() or '..' in p.parts or p.as_posix() != rel or not p.parts:
            raise ValueError('unsafe manifest path')
        if rel in expected_paths:
            raise ValueError('duplicate manifest path')
        expected_paths.add(rel)
        target = base.joinpath(*p.parts)
        current = base
        for part in p.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError('symlink in packet path: ' + rel)
        if not target.resolve().is_relative_to(base):
            raise ValueError('path escaped packet')
        good, reason = check_entry(target, entry['size'], entry['sha256'])
        if not good:
            raise ValueError(rel + ': ' + reason)
        total += entry['size']
    actual = set()
    for directory, dirs, files in os.walk(base, followlinks=False):
        for name in dirs + files:
            p = Path(directory) / name
            if p.is_symlink():
                raise ValueError('unexpected symlink: ' + str(p.relative_to(base)))
        for name in files:
            actual.add((Path(directory) / name).relative_to(base).as_posix())
    if actual != expected_paths:
        raise ValueError('packet file set mismatch; missing=' + repr(sorted(expected_paths-actual))
                         + '; extra=' + repr(sorted(actual-expected_paths)))
    if len(actual) != data['file_count'] or total != data['total_bytes']:
        raise ValueError('manifest totals mismatch')
    return {'artifact_integrity': 'matched', 'files': len(actual), 'bytes': total,
            'mathematical_gate': 'not evaluated'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for key in ['packet', 'manifest', 'final', 'report']:
        p.add_argument('--'+key, type=Path, required=True)
    for key in ['manifest', 'final', 'report']:
        p.add_argument('--'+key+'-sha256', required=True)
    a = p.parse_args()
    try:
        result = verify(a.packet, a.manifest, a.final, a.report,
                        a.manifest_sha256, a.final_sha256, a.report_sha256)
    except (OSError, ValueError, KeyError, TypeError) as e:
        print('ARTIFACT CHECK FAILED: '+str(e), file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
