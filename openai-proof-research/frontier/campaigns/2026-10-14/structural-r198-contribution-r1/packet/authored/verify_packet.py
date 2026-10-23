#!/usr/bin/env python3
"""Read-only exact packet verifier. Explicit detached anchors are mandatory.
Does not create, chmod, repair, regenerate, or update any packet/report/manifest.
Successful artifact verification is not a mathematical or semantic-reading grade.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def regular_bytes(path):
    mode = path.lstat().st_mode
    need(stat.S_ISREG(mode), 'Not a regular non-symlink file: ' + str(path))
    return path.read_bytes(), stat.S_IMODE(mode)


def canonical_relative(value, directory=False):
    need(isinstance(value, str), 'Non-string member path')
    if directory and value == '.':
        return value
    p = PurePosixPath(value)
    need(not p.is_absolute() and value == p.as_posix() and
         all(part not in ('', '.', '..') for part in value.split('/')) and
         '\\' not in value, 'Unsafe or noncanonical member: ' + value)
    return value


def verify(packet, report, manifest_sha256, final_sha256, report_sha256):
    for name, value in [('manifest', manifest_sha256), ('FINAL', final_sha256), ('REPORT', report_sha256)]:
        need(bool(re.fullmatch('[0-9a-f]{64}', value)), 'Invalid explicit ' + name + ' anchor')
    need(stat.S_ISDIR(packet.lstat().st_mode), 'Packet is not a non-symlink directory')
    need(not report.resolve().is_relative_to(packet.resolve()), 'REPORT must be outside packet')
    mb, mmode = regular_bytes(packet / 'MANIFEST.json')
    need(mmode == 0o644, 'Manifest mode mismatch')
    need(digest(mb) == manifest_sha256, 'Detached manifest mismatch')
    manifest = json.loads(mb)
    expected_files = {}
    expected_dirs = {}
    for e in manifest['files']:
        p = canonical_relative(e['path'])
        need(p not in expected_files and p != 'MANIFEST.json', 'Duplicate/self manifest member')
        need(isinstance(e['bytes'], int) and e['bytes'] >= 0, 'Invalid byte size')
        need(isinstance(e['mode'], int), 'Invalid file mode')
        need(bool(re.fullmatch('[0-9a-f]{64}', e['sha256'])), 'Invalid member hash')
        expected_files[p] = e
    for e in manifest['directories']:
        p = canonical_relative(e['path'], directory=True)
        need(p not in expected_dirs, 'Duplicate directory member')
        expected_dirs[p] = e['mode']
    need('.' in expected_dirs and 'FINAL.md' in expected_files, 'Missing root or FINAL member')
    actual_files, actual_dirs = set(), {}
    for root, dirs, files in os.walk(packet, followlinks=False):
        root = Path(root)
        st = root.lstat()
        need(stat.S_ISDIR(st.st_mode), 'Non-directory or symlink directory')
        actual_dirs[root.relative_to(packet).as_posix()] = stat.S_IMODE(st.st_mode)
        for name in dirs:
            need(stat.S_ISDIR((root / name).lstat().st_mode), 'Non-directory/symlink in directory list')
        for name in files:
            p = root / name
            need(stat.S_ISREG(p.lstat().st_mode), 'Nonregular/symlink packet member')
            actual_files.add(p.relative_to(packet).as_posix())
    need(actual_files == set(expected_files) | {'MANIFEST.json'}, 'Exact file membership mismatch')
    need(actual_dirs == expected_dirs, 'Exact directory membership/mode mismatch')
    total = 0
    for name, e in expected_files.items():
        b, mode = regular_bytes(packet / name)
        need(mode == e['mode'], 'Member mode mismatch: ' + name)
        need(len(b) == e['bytes'], 'Member length mismatch: ' + name)
        need(digest(b) == e['sha256'], 'Member hash mismatch: ' + name)
        total += len(b)
    fb, _ = regular_bytes(packet / 'FINAL.md')
    need(digest(fb) == final_sha256, 'Detached FINAL mismatch')
    rb, rmode = regular_bytes(report)
    need(rmode == manifest.get('outside_report_mode', 0o644), 'Outside REPORT mode mismatch')
    need(digest(rb) == report_sha256, 'Detached REPORT mismatch')
    return {'artifact_verification': 'accepted', 'selected_files': len(expected_files),
            'selected_bytes': total, 'selected_directories': len(expected_dirs),
            'manifest_is_separately_anchored': True, 'read_only': True,
            'mathematical_grade': 'not supplied by this verifier'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    try:
        result = verify(a.packet, a.report, a.manifest_sha256, a.final_sha256, a.report_sha256)
    except Exception as e:
        print(json.dumps({'artifact_verification': 'rejected', 'error': str(e), 'read_only': True}))
        return 1
    print(json.dumps(result))
    return 0


if __name__ == '__main__':
    sys.exit(main())
