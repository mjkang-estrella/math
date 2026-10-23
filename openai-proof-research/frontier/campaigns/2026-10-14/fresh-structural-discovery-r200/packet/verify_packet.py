#!/usr/bin/env python3
"""Read-only artifact comparison. No mathematical or contribution verdict."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def mode(path):
    return format(stat.S_IMODE(path.stat().st_mode), '04o')

def require(condition, message):
    if not condition:
        raise ValueError(message)

def safe_relative(value):
    p = PurePosixPath(value)
    require(not p.is_absolute() and '..' not in p.parts and str(p) == value,
            'noncanonical or escaping manifest path')
    return p

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--report', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    for v in (args.manifest_sha256, args.final_sha256, args.report_sha256):
        require(re.fullmatch('[0-9a-f]{64}', v) is not None, 'invalid explicit anchor')
    root = Path(args.root)
    require(root.is_dir() and not root.is_symlink(), 'invalid packet directory')
    manifest = root / 'MANIFEST.json'
    require(manifest.is_file() and not manifest.is_symlink(), 'missing manifest')
    require(digest(manifest) == args.manifest_sha256, 'manifest anchor mismatch')
    doc = json.loads(manifest.read_bytes())
    require(doc['schema'] == 'r200.exact-selection.v1', 'unknown selection schema')
    require(mode(manifest) == doc['manifest_mode'], 'manifest mode mismatch')
    entries = doc['files']
    names = [e['path'] for e in entries]
    require(names == sorted(set(names)), 'file selection is not sorted and unique')
    directories = doc['directories']
    dnames = [e['path'] for e in directories]
    require(dnames == sorted(set(dnames)), 'directory selection is not sorted and unique')
    for value in names + dnames:
        safe_relative(value)
    actual_files, actual_dirs = set(), {'.'}
    for here, dirs, files in os.walk(root, topdown=True, followlinks=False):
        for name in dirs + files:
            p = Path(here) / name
            require(not p.is_symlink(), 'symlink in exact packet')
        actual_dirs.update((Path(here) / d).relative_to(root).as_posix() for d in dirs)
        actual_files.update((Path(here) / f).relative_to(root).as_posix() for f in files)
    require(actual_files == set(names) | {'MANIFEST.json'}, 'exact file selection mismatch')
    require(actual_dirs == set(dnames), 'exact directory selection mismatch')
    for e in directories:
        require(mode(root / e['path']) == e['mode'], 'directory mode mismatch: ' + e['path'])
    for e in entries:
        p = root / e['path']
        require(p.is_file(), 'nonregular selected file: ' + e['path'])
        require(mode(p) == e['mode'], 'file mode mismatch: ' + e['path'])
        require(p.stat().st_size == e['bytes'], 'file length mismatch: ' + e['path'])
        require(digest(p) == e['sha256'], 'file digest mismatch: ' + e['path'])
    final = root / doc['final']
    require(doc['final'] in names, 'FINAL not selected')
    require(digest(final) == args.final_sha256, 'FINAL anchor mismatch')
    report = Path(args.report)
    require(report.is_file() and not report.is_symlink(), 'invalid outside REPORT')
    require(root.resolve() not in report.resolve().parents, 'REPORT must be outside packet')
    require(mode(report) == doc['outside_report_mode'], 'outside REPORT mode mismatch')
    require(digest(report) == args.report_sha256, 'outside REPORT anchor mismatch')
    print(json.dumps({'artifact_comparison': 'match', 'selected_files': len(names),
                      'selected_directories': len(dnames),
                      'scope': 'bytes, lengths, modes, exact selection, detached anchors only'}))

if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print('Artifact comparison rejected: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
