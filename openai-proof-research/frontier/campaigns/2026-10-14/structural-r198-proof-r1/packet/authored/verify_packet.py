#!/usr/bin/env python3
"""Read-only exact-membership/mode/hash verifier; no mathematical validation."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def regular(path):
    mode = path.lstat().st_mode
    require(stat.S_ISREG(mode), 'not an ordinary file: ' + str(path))
    return stat.S_IMODE(mode)


def safe_name(name, directory=False):
    require(isinstance(name, str), 'non-string member path')
    if directory and name == '.':
        return name
    pp = PurePosixPath(name)
    require(not pp.is_absolute() and name not in ('', '.') and
            '..' not in pp.parts and pp.as_posix() == name and '\\' not in name,
            'unsafe member path: ' + repr(name))
    return name


def inventory(packet):
    root_mode = packet.lstat().st_mode
    require(stat.S_ISDIR(root_mode), 'packet root is not an ordinary directory')
    dirs = {'.': stat.S_IMODE(root_mode)}
    files = {}
    for base, ds, fs in os.walk(packet, followlinks=False):
        for name in ds:
            p = Path(base) / name
            mode = p.lstat().st_mode
            require(stat.S_ISDIR(mode), 'non-directory or symlink: ' + str(p))
            dirs[p.relative_to(packet).as_posix()] = stat.S_IMODE(mode)
        for name in fs:
            p = Path(base) / name
            mode = regular(p)
            b = p.read_bytes()
            files[p.relative_to(packet).as_posix()] = {
                'bytes': len(b), 'mode': mode, 'sha256': sha(b)}
    return dirs, files


def verify(packet, report, manifest_sha256, final_sha256, report_sha256):
    packet, report = Path(packet), Path(report)
    for anchor in (manifest_sha256, final_sha256, report_sha256):
        require(re.fullmatch('[0-9a-f]{64}', anchor) is not None,
                'explicit lowercase SHA256 anchor required')
    require(regular(packet / 'MANIFEST.json') == 0o644, 'manifest mode')
    mb = (packet / 'MANIFEST.json').read_bytes()
    require(sha(mb) == manifest_sha256, 'manifest detached anchor mismatch')
    manifest = json.loads(mb)
    require(manifest['schema'] == 'structural-r198-proof-r1-selected-v1', 'schema mismatch')
    expected_files, expected_dirs = {}, {}
    for entry in manifest['files']:
        name = safe_name(entry['path'])
        require(name not in expected_files and name != 'MANIFEST.json', 'duplicate/self manifest member')
        expected_files[name] = {k: entry[k] for k in ('bytes', 'mode', 'sha256')}
    for entry in manifest['directories']:
        name = safe_name(entry['path'], directory=True)
        require(name not in expected_dirs, 'duplicate directory member')
        expected_dirs[name] = entry['mode']
    actual_dirs, actual_files = inventory(packet)
    require(actual_dirs == expected_dirs, 'exact directory membership/mode mismatch')
    require(set(actual_files) == set(expected_files) | {'MANIFEST.json'},
            'exact file membership mismatch')
    for name, expected in expected_files.items():
        require(actual_files[name] == expected, 'member bytes/mode/hash mismatch: ' + name)
    require('FINAL.md' in expected_files, 'FINAL not a member')
    require(actual_files['FINAL.md']['sha256'] == final_sha256, 'FINAL detached anchor mismatch')
    require(packet.resolve() not in report.resolve().parents, 'REPORT must be outside packet')
    require(regular(report) == manifest['outside_report_mode'], 'REPORT mode mismatch')
    require(sha(report.read_bytes()) == report_sha256, 'REPORT detached anchor mismatch')
    return {'ok': True, 'artifact_only': True, 'files': len(expected_files),
            'selected_bytes': sum(e['bytes'] for e in expected_files.values()),
            'directories': len(expected_dirs), 'manifest_separately_anchored': True,
            'final_sha256': final_sha256, 'manifest_sha256': manifest_sha256,
            'report_sha256': report_sha256}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', required=True)
    parser.add_argument('--report', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    a = parser.parse_args()
    try:
        answer = verify(a.packet, a.report, a.manifest_sha256, a.final_sha256, a.report_sha256)
    except (ValueError, OSError, KeyError, TypeError) as e:
        parser.exit(1, json.dumps({'ok': False, 'artifact_only': True, 'error': str(e)}) + '\n')
    print(json.dumps(answer, indent=2))


if __name__ == '__main__':
    main()
