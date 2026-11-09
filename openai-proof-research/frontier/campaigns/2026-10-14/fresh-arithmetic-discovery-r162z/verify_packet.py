#!/usr/bin/env python3
"""Read-only verification. Detached anchors MUST be supplied explicitly."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(root, name):
    p = Path(name)
    if p.is_absolute() or not p.parts or any(x in ('..', '.') for x in p.parts):
        raise ValueError('unsafe relative path')
    cur = root
    for part in p.parts:
        cur = cur / part
        if cur.is_symlink():
            raise ValueError('symlink in selection: ' + name)
    return cur


def selected(root, roots, extras):
    names = set()
    for name in roots:
        base = safe(root, name)
        if not base.is_dir():
            raise ValueError('missing selected directory: ' + name)
        for current, dirs, files in os.walk(base, followlinks=False):
            for d in dirs:
                if (Path(current) / d).is_symlink():
                    raise ValueError('symlink directory')
            for f in files:
                p = Path(current) / f
                rel = p.relative_to(root).as_posix()
                if not safe(root, rel).is_file():
                    raise ValueError('nonregular selection member')
                names.add(rel)
    for name in extras:
        if not safe(root, name).is_file():
            raise ValueError('missing extra file: ' + name)
        names.add(name)
    return names


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    root = Path(args.root).resolve(strict=True)
    for filename, expected in [('MANIFEST.json', args.manifest_sha256),
                               ('FINAL.md', args.final_sha256),
                               ('REPORT.md', args.report_sha256)]:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('invalid explicit anchor')
        if sha(safe(root, filename).read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + filename)
    manifest = json.loads(safe(root, 'MANIFEST.json').read_text())
    if manifest['version'] != 1:
        raise ValueError('unsupported manifest version')
    entries = manifest['files']
    expected_names = {entry['path'] for entry in entries}
    if len(entries) != len(expected_names):
        raise ValueError('duplicate manifest member')
    actual_names = selected(root, manifest['selected_roots'], manifest['extra_files'])
    if actual_names != expected_names:
        raise ValueError('exact selection membership mismatch')
    total = 0
    for entry in entries:
        data = safe(root, entry['path']).read_bytes()
        if len(data) != entry['bytes'] or sha(data) != entry['sha256']:
            raise ValueError('payload mismatch: ' + entry['path'])
        total += len(data)
    print(json.dumps({'artifact_integrity': 'PASS', 'files': len(entries),
                      'bytes': total, 'mathematical_gate': False}))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        sys.exit(1)
