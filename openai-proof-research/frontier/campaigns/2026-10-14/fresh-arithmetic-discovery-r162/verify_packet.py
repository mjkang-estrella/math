#!/usr/bin/env python3
"""Read-only packet artifact verifier. Requires three external SHA256 anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys

def digest(data):
    return hashlib.sha256(data).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def regular(path):
    require(not path.is_symlink() and path.is_file(), "not a regular non-symlink file: " + str(path))
    return path.read_bytes()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet-root', required=True)
    ap.add_argument('--report-path', required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    for name in ('final_sha256', 'manifest_sha256', 'report_sha256'):
        require(re.fullmatch('[0-9a-f]{64}', getattr(args, name)) is not None, 'invalid explicit ' + name)
    root = Path(args.packet_root).absolute()
    report = Path(args.report_path).absolute()
    for p in (root, report):
        require(not any(q.is_symlink() for q in (p, *p.parents)), 'symlink in anchor path')
    require(root.is_dir(), 'packet root is not a directory')
    require(root not in report.parents, 'REPORT must be outside packet')
    final_data = regular(root / 'FINAL.md')
    manifest_data = regular(root / 'MANIFEST.json')
    report_data = regular(report)
    require(digest(final_data) == args.final_sha256, 'FINAL anchor mismatch')
    require(digest(manifest_data) == args.manifest_sha256, 'MANIFEST anchor mismatch')
    require(digest(report_data) == args.report_sha256, 'REPORT anchor mismatch')
    doc = json.loads(manifest_data)
    require(doc.get('format') == 'r162-exact-packet-v1', 'unsupported manifest format')
    entries = doc.get('files')
    require(isinstance(entries, list), 'manifest files must be a list')
    expected = set()
    total = 0
    for ent in entries:
        rel = ent['path']
        p = PurePosixPath(rel)
        require(isinstance(rel, str) and rel == p.as_posix() and not p.is_absolute() and
                all(x not in ('', '.', '..') for x in rel.split('/')) and '\\' not in rel,
                'unsafe member path')
        require(rel != 'MANIFEST.json' and rel not in expected, 'self/duplicate member')
        require(type(ent['bytes']) is int and ent['bytes'] >= 0, 'bad byte count')
        require(re.fullmatch('[0-9a-f]{64}', ent['sha256']) is not None, 'bad member digest')
        member = root.joinpath(*p.parts)
        require(not any(q.is_symlink() for q in (member, *member.parents)), 'symlink in member path')
        data = regular(member)
        require(len(data) == ent['bytes'], 'member length mismatch: ' + rel)
        require(digest(data) == ent['sha256'], 'member digest mismatch: ' + rel)
        expected.add(rel)
        total += len(data)
    actual = set()
    for parent, dirs, files in os.walk(root, followlinks=False):
        for name in dirs:
            require(not (Path(parent) / name).is_symlink(), 'symlink directory in packet')
        for name in files:
            p = Path(parent) / name
            require(p.is_file() and not p.is_symlink(), 'nonregular packet member')
            actual.add(p.relative_to(root).as_posix())
    require(actual == expected | {'MANIFEST.json'}, 'packet membership differs from manifest')
    print(json.dumps({'artifact_verification': 'matched', 'members': len(expected),
                      'member_bytes': total, 'mathematical_gate': False}, sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        print('ARTIFACT VERIFICATION FAILED: ' + str(exc), file=sys.stderr)
        sys.exit(1)
